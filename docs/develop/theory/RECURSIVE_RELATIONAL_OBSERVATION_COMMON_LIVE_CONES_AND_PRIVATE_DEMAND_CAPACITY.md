# Common live cones and private-demand capacity in stationary threshold control

## 1. Original graph and conditional support interfaces

Fix the original threshold parameters

$$
n\ge6,\qquad 3\le k\le n-2,\qquad
K=k,\quad L=n-k+1,\quad n=K+L-1,
$$

and distinct positive integer positions $A=\{s_1<\cdots<s_n\}$. Write

$$
c_i=s_i+4,\qquad C_X=\sum_{i\in X}c_i,\qquad W=C_{[n]},
\qquad V=\{0,\ldots,K-1\}\times\{0,\ldots,L-1\},\quad G=KL.
\tag{CL.1}
$$

One graph has a finite installed running-state set $Q$, a fixed running
start, two distinct terminals $\mathsf0,\mathsf1$, and at every $q\in Q$
one fixed coordinate $i(q)\in[n]$ and two fixed successors
$\delta(q,0),\delta(q,1)$. Its entire changing configuration is its
current state. On every $\theta\in\{0,1\}^n$ the actual run terminates
with $\mathbf1_{\{|\theta|\ge k\}}$ and satisfies, on that same run,

$$
t_P(\theta)\le n,\qquad
J_P(\theta)=\sum_{\text{actual visits to }q}c_{i(q)}\le W.
\tag{CL.2}
$$

Every installed running state counts in $m=|Q|$, including unused states
and states reached only after certification. Every actual invocation,
including a repeated or certified query, is paid. Adaptive coordinate
orders, sharing and syntactic cycles are allowed; only actual runs must
terminate. A syntactic path with inconsistent replies to one coordinate
need not be actual. No order, clock, counter, history, computed address,
block entry or auxiliary changing register is supplied.

Let **SI** denote *Actual support incidence and the exact count relaxation
in native threshold preparation*. The following local interfaces are
those explicitly stated in SI Section 2, with its original full-fiber
and double-cap hypotheses. Their nested attributions are PCA Theorems
34.3 and 35.1, PE Lemma 4.1, and WTF Convention 6.1 and Theorem 9.1.
They are conditional suppliers here; the nested texts are not additional
premises authenticated independently by this companion.

A history ends immediately before a query and is an actual finite prefix.
Its support $S$ is the set of already read coordinates; its exposed
assignment has $h$ ones and $z$ zeros. It is live precisely when
$(h,z)\in V$. At live histories the next query is fresh. Properly nested
supports cannot occur at a common live state. Different supports with
equal hits cannot occur at a common state, and equal supports with
unequal hits cannot occur there. Finally distinct hosted count cells can
be oriented as

$$
p=(h,z),\quad p'=(g,w),\quad h<g,
\qquad g-h\ge2,\quad z-w\ge2.
\tag{CL.3}
$$

The deductions below use these displayed interfaces on the one original
graph. They impose no further class hypothesis on that graph.

For $p=(h,z)\in V$, let $F_p$ be its set of actual live ending states,
and $\mathcal S_p$ its family of actual exposed supports. Put

$$
b_p=|F_p|,\qquad a_p=|\mathcal S_p|,\qquad e_p=b_p-1.
\tag{CL.4}
$$

Every earlier prefix of a live history is live. Freshness therefore gives
depth $d=h+z$ and $|S|=d$. Any reply word with final live counts is actual:
inductively every partial count is live, the current query is fresh, and
the requested reply can be fixed on that unread coordinate. Any completion
of the resulting exposed assignment follows the entire prefix by
determinism. In particular every cell has a history. At fixed $p,q$, two
different supports would contradict the equal-hit exclusion, so its support
is unique; denote it by $S_p(q)$. The resulting surjection from hosts to
supports gives

$$
b_p\ge a_p\ge1.
\tag{CL.5}
$$

If $(p,S,q)$ is an actual live occurrence, put
$p_\varepsilon=(h+\varepsilon,z+1-\varepsilon)$. Whenever
$p_\varepsilon\in V$, fixing the fresh reply $\varepsilon$ produces
an actual live occurrence

$$
(p_\varepsilon,S\cup\{i(q)\},\delta(q,\varepsilon)).
\tag{CL.6}
$$

A live child cannot be a terminal, since both outputs have completions.
This is the fixed-successor assertion of SI Theorem 2.2. Each occurrence
is realized separately on a completion of its own exposed assignment;
no common completing input for different old histories is required.

## 2. Common cuts and exact incidence on one graph

Write $V_d=\{(h,z)\in V:h+z=d\}$. A depth $d<n$ is common-support
when all actual live histories there have one support $T_d$.
Equivalently every cell on that diagonal has a singleton support family.
For the nontrivial direction, adjacent cells $(h,z)$ and $(h+1,z-1)$
have the common live parent $(h,z-1)$. One actual history of that parent
has two live children with the same support by (CL.6). If both child
families are singletons, those singleton supports coincide. The admissible
hit counts on a diagonal form an integer interval, so these adjacent
comparisons connect the entire diagonal. This argument needs no singleton
assumption at the parents. Depth zero is common, with $T_0=\varnothing$.

Adjoin the formal endpoint $n$ with $T_n=[n]$ and list all common depths
and that endpoint. Let $\mathcal C$ be the actual common depths and
$\mathcal B$ the gaps between consecutive entries. For $B=(a,b)$ put

$$
\begin{aligned}
\beta_B&=b-a,& X_B&=T_b\setminus T_a,\\
V_B&=\{p\in V:a<h(p)+z(p)<b\},&
Q_B&=\bigcup_{p\in V_B}F_p,\\
E_B&=\sum_{p\in V_B}(b_p-1),&
D_B&=\sum_{q\in Q_B}\bigl(|\{p\in V_B:q\in F_p\}|-1\bigr).
\end{aligned}
\tag{CL.7}
$$

An empty interior contributes empty sets and zero sums. Set

$$
\begin{aligned}
Q_{\rm live}&=\bigcup_{p\in V}F_p,& u&=|Q\setminus Q_{\rm live}|,\\
E&=\sum_{p\in V}(b_p-1),&
D&=\sum_{q\in Q_{\rm live}}\bigl(|\{p\in V:q\in F_p\}|-1\bigr),\\
E_a&=\sum_{p\in V_a}(b_p-1)\quad(a\in\mathcal C),&
E_{\rm cut}&=\sum_{a\in\mathcal C}E_a.
\end{aligned}
\tag{CL.8}
$$

These distinguish support families $\mathcal S_p$, host families $F_p$,
excess incidences $E$, duplicate cell incidences $D$, and genuinely
never-live states $u$. A state live on one input and certified on another
belongs to $Q_{\rm live}$ and contributes nothing to $u$.

**Lemma 2.1 (actual extension and envelopes; SI Lemma 9.2).** Every live
history extends to every specified later live depth up to $n-1$. Common
supports form a strictly increasing chain with $|T_a|=a$. At any live
occurrence of depth $a\le d<b$ in the range of $B=(a,b)$,

$$
T_a\subseteq S\subsetneq T_b,\qquad
i(q)\in T_b\setminus S\subseteq X_B.
\tag{CL.9}
$$

Proof. Before depth $n-1$ a live cell is not $(K-1,L-1)$, so at least
one reply has a live child. Repeated use of (CL.6) gives the desired
extension, with a completion of each resulting fresh-coordinate
assignment realizing the entire prefix. A live ancestor at depth $a$
gives $T_a\subseteq S$. If $b<n$, extend through depth $b$; this
includes the next query and gives the other assertions. If $b=n$,
freshness and $T_n=[n]$ give them directly. Applying this to common
depths proves containment of their supports, and their different
cardinalities make containment strict. There is no live occurrence at
the formal endpoint $n$. $\square$

**Lemma 2.2 (localization and counting; SI Theorem 9.3).** The blocks
$X_B$ partition $[n]$. The interior pools $Q_B$ and all cut pools
$\bigcup_{p\in V_a}F_p$ are pairwise disjoint. A cut state hosts exactly
one count cell. Consequently

$$
\begin{gathered}
|Q_B|=|V_B|+E_B-D_B,\\
D=\sum_BD_B,\qquad
E=E_{\rm cut}+\sum_BE_B,\\
m-G=E-D+u=E_{\rm cut}+u+\sum_B(E_B-D_B).
\end{gathered}
\tag{CL.10}
$$

Proof. At a common depth supports coincide; unequal-hit cells cannot
share a state. Every earlier live support is a proper subset of that
common support by extension, and every later one properly contains it
by ancestry. Nested-support exclusion separates a cut state from all
other depths. The chain from $\varnothing$ to $[n]$ has disjoint
successive differences $X_B$. By (CL.9) a live state's one fixed label
belongs to its range's block, so it cannot lie in two different ranges.
This proves localization and the assertions about cuts.

Double-counting the finite cell-state incidences inside a pool gives
$\sum_{p\in V_B}b_p=|Q_B|+D_B$, proving the first identity. Globally
$\sum_pb_p=G+E=|Q_{\rm live}|+D$ and
$m=|Q_{\rm live}|+u$. Localized sharing gives $D=\sum_BD_B$ and the
partition of cells gives $E=E_{\rm cut}+\sum_BE_B$. These prove (CL.10).
Every state and incidence has its original meaning; no certified visit
is suppressed. $\square$

For completeness the same decomposition respects the original installed
coordinate vector. Put $m_i=|\{q:i(q)=i\}|$, $m(X)=\sum_{i\in X}m_i$,
$u_B=|\{q\in Q\setminus Q_{\rm live}:i(q)\in X_B\}|$, and
$g_B=|V_a|+|V_B|$. Localization partitions the states with label in
$X_B$ into its lower cut pool, its interior pool, and those counted by
$u_B$. Hence

$$
m(X_B)-g_B=E_a+E_B-D_B+u_B,\qquad
\sum_Bu_B=u,\quad \sum_Bg_B=G.
\tag{CL.11}
$$

These are finite incidence identities, not independently allocated
residual graphs. Certified traffic can cross the live envelopes and
remains paid on its original full run.

Every internal depth of a consecutive gap is noncommon. The diagonal
argument above and (CL.5) therefore give the credited baseline

$$
e_d:=\sum_{p\in V_d}(b_p-1)\ge1
\qquad(a<d<b).
\tag{CL.12}
$$

## 3. Union capacity of a common live cone

**Theorem 3.1 (simultaneous support union).** Fix a gap $B=(a,b)$,
any $q\in Q_B$, and any subcollection $\mathcal I$ of at least two
distinct interior count cells hosted by $q$. Let

$$
H=\max_{(h,z)\in\mathcal I}h,\quad
Z=\max_{(h,z)\in\mathcal I}z,\quad
U=\bigcup_{p\in\mathcal I}S_p(q),\quad \ell=n-b.
$$

Then

$$
|T_b\setminus U|\ge n-H-Z,\qquad
|U|\le H+Z-\ell.
\tag{CL.13}
$$

Proof. Choose one actual history for each indexed occurrence. Put
$A_1=K-1-H$, $A_0=L-1-Z$, and
$t=A_1+A_0=n-1-H-Z\ge0$. Append the same reply word
$1^{A_1}0^{A_0}$ to each history. Every count prefix is live on
each: its hit count is at most $H+A_1=K-1$ and its zero count at
most $Z+A_0=L-1$.

Induction gives separately actual extensions ending at the same state
$q_j$ after $j$ appended replies, $0\le j\le t$. While live the next
query is fresh, and the requested value has a completion of each
history's own exposed assignment. The fixed successor is the same for
all these histories. Their different original count cells remain
different after the common increment.

All these occurrences stay inside $B$. If one first reached the upper
common depth $b<n$, it would share its state with a distinct live cell,
contradicting Lemma 2.2. It cannot pass that depth without reaching it.
If $b=n$, no live occurrence can reach $b$ at all. Depth only increases,
so no occurrence leaves through the lower boundary. By (CL.9) every
$i(q_j)$ therefore belongs to $X_B\subseteq T_b$.

The fixed reply sequence makes the already appended query coordinates
common to all the histories. Freshness at each occurrence implies that
$i(q_j)$ is outside every original support and outside all earlier
appended coordinates. Thus $i(q_0),\ldots,i(q_t)$ are $t+1$ distinct
members of $T_b\setminus U$. The query at $q_t$ is available and fresh;
its reply need not keep all occurrences live. Hence
$|T_b\setminus U|\ge t+1=n-H-Z$, which is (CL.13) because $|T_b|=b$.
This includes $t=0$ and the final query before certification. It uses
no common input for the old histories and no syntactic acyclicity.
$\square$

**Corollary 3.2 (private-size and intersection bounds).** For a shared
pair oriented as in (CL.3), set
$r=g-h$, $s=z-w$, $S=S_p(q)$, $T=S_{p'}(q)$ and $\ell=n-b$.
Then

$$
\begin{aligned}
|S\cup T|&\le g+z-\ell,& |T\setminus S|&\le r-\ell,\\
|S\setminus T|&\le s-\ell,& |S\cap T|&\ge h+w+\ell,\\
r,s&\ge\max(2,\ell+1).
\end{aligned}
\tag{CL.14}
$$

Proof. Apply (CL.13) with $H=g,Z=z$. Subtract $|S|=h+z$ or
$|T|=g+w$ from its union bound for the two private-size bounds.
Inclusion-exclusion gives the intersection bound. The support exclusions
make $S,T$ incomparable, so both private sets are nonempty and
$r,s\ge\ell+1$; combine this with (CL.3). Inclusion-exclusion is the
standard finite-set identity. The application here retains the union
restriction for every larger hosted subcollection as well. $\square$

## 4. Actual private separation at a join cell

**Theorem 4.1 (two actual join supports).** In Corollary 3.2 suppose

$$
r\le K-g,\qquad s\le L-z.
\tag{CL.15}
$$

Then $v=(g,z)\in V_B$, and it has actual live supports $S^+,T^+$ with

$$
S^+\cap(S\cup T)=S,\qquad T^+\cap(S\cup T)=T.
\tag{CL.16}
$$

Thus for every $x\in S\setminus T$ and $y\in T\setminus S$ the
two supports realize both $x$-in/$y$-out and $y$-in/$x$-out.

Proof. The original bounds $g\le K-1,z\le L-1$ make $v$ live.
By (CL.14), $r,s\ge\ell+1$, where $\ell=n-b$. Conditions (CL.15)
give $g+r\le K,z+s\le L$, whence

$$
g+z\le K+L-r-s
       =n+1-r-s\le b-\ell-1\le b-1.
\tag{CL.17}
$$

Also $g+z=(h+z)+r>a$, proving $v\in V_B$.

From the occurrence at $p,q$ follow $1^r$. Its own counts stay live
through the last reply, ending at $(g,z)$. Before the query with
$j$ previous appended replies, $0\le j<r$, the original occurrence
at $p',q$ can separately follow $1^j$ while live, because
$g+j\le g+r-1\le K-1$. The two actual extensions have the same fixed
state at that step. Its label is fresh for both, hence outside $S\cup T$
and outside all previously appended coordinates. The retained lower
history therefore ends with $S^+=S\cup R_1$, where
$R_1\cap(S\cup T)=\varnothing$.

Independently follow $0^s$ from the occurrence at $p',q$. It stays live
through its last reply and ends at $(g,w+s)=(g,z)$. At every proper
prefix of length $j<s$, the original lower occurrence can separately
follow $0^j$ while live, since $z+j\le z+s-1\le L-1$. Fixed successors
again make every queried label fresh for both. Thus the retained upper
history ends with $T^+=T\cup R_0$, where
$R_0\cap(S\cup T)=\varnothing$.

On either construction the helper's last reply may certify it.
Freshness was used only before that reply, when both occurrences were
live. Each retained extension is actual on its own completion; their
completions need not agree, and the two constructions need not use the
same appended coordinates. Their intersections prove (CL.16).
Incomparability supplies private elements, so these supports are
different and require different hosts at the fixed cell by (CL.5).
No behavior after certification has been prescribed or erased.
$\square$

The eligibility conditions (CL.15) are sufficient for this construction.
Sharing near a hit or zero boundary can fail them. Such sharing is still
part of the original graph and is still counted in $D_B$.

## 5. All private demands at one cell

For every interior $v=(g,z)$ form the finite simple undirected graph
$\Gamma_v$ on the entire coordinate set $X_B$. An unordered pair
$\{x,y\}$ is an edge if some actual shared state $q\in Q_B$ hosts
an oriented pair $p=(h,z),p'=(g,w)$ satisfying (CL.15), with
$x\in S_p(q)\setminus S_{p'}(q)$ and
$y\in S_{p'}(q)\setminus S_p(q)$, or conversely. Include all such
private cross-pairs from all eligible witnesses. The private coordinates
are in $X_B$ by (CL.9). Repeated generation of an edge leaves one edge.
An isolated coordinate remains a vertex. Write $\chi_v$ for the minimum
number of colors in a proper coloring; an edgeless graph on the nonempty
$X_B$ has $\chi_v=1$.

For a positive integer $c$ define

$$
\tau(c)=\min\{j\ge1:\tbinom{j}{\lfloor j/2\rfloor}\ge c\}.
\tag{CL.18}
$$

This is finite. For $c=1$, $j=1$ suffices. For $c\ge2$ the middle
coefficient in row $c$ is at least $\binom c1=c$: consecutive binomial
coefficients increase to the middle, as follows from their ratio
$(c-j)/(j+1)$. No asymptotic estimate is needed.

Let $d=g+z$ and $t_v=d-a$, so $1\le t_v\le\beta_B-1$. When
$\Gamma_v$ has an edge, put

$$
\begin{aligned}
M_v&=\max_{\substack{R\subseteq X_B\\|R|=t_v}}
       |\{e\in E(\Gamma_v):|e\cap R|=1\}|,\\
\kappa_v&=\max\left(\tau(\chi_v),
              \left\lceil\frac{2|E(\Gamma_v)|}{M_v}\right\rceil\right).
\end{aligned}
\tag{CL.19}
$$

Here $M_v>0$: choose one edge, include one endpoint and exclude the other,
and fill $t_v-1$ places from the remaining $\beta_B-2$ coordinates.
For an edgeless $\Gamma_v$ set $\kappa_v=1$, without a ratio involving
zero. These are finite mathematical definitions; no enumeration,
optimizer or new resource is provided to the running graph.

**Theorem 5.1 (combined membership and cut capacity).** For every
interior cell,

$$
b_v\ge a_v\ge\kappa_v.
\tag{CL.20}
$$

More explicitly, writing $A=a_v$,

$$
\chi_v\le\binom{A}{\lfloor A/2\rfloor},\qquad
2|E(\Gamma_v)|\le A M_v\quad\text{if }E(\Gamma_v)\ne\varnothing.
\tag{CL.21}
$$

Proof of the membership bound. List the distinct actual supports at $v$
as $U_1,\ldots,U_A$. For $x\in X_B$ give it the membership code
$C_x=\{j\in[A]:x\in U_j\}$. By Theorem 4.1 an edge $\{x,y\}$
has one actual support containing $x$ and omitting $y$, and another
containing $y$ and omitting $x$. Thus both $C_x\setminus C_y$ and
$C_y\setminus C_x$ are nonempty: adjacent codes are incomparable.

We use the standard symmetric-chain decomposition of the Boolean lattice,
with its full elementary proof. At rank zero there is one chain consisting
of the empty set. Suppose the subsets of an $A$-element set have been
partitioned into chains
$U_k\subset U_{k+1}\subset\cdots\subset U_{A-k}$, where $|U_j|=j$.
Adjoin a new element $x$ and replace each such chain by

$$
U_k,\ldots,U_{A-k},U_{A-k}\cup\{x\},
\qquad
U_k\cup\{x\},\ldots,U_{A-k-1}\cup\{x\},
\tag{CL.22}
$$

omitting the second chain if its range is empty. Each is a chain whose
endpoint ranks sum to $A+1$, and together they partition exactly the
sets of the old chain with and without $x$. Applying this replacement
to every old chain proves the decomposition inductively. Every symmetric
chain for an $A$-element ground set contains exactly one set of rank
$\lfloor A/2\rfloor$. There are consequently
$\binom A{\lfloor A/2\rfloor}$ chains.

Color $x\in X_B$ by the chain containing $C_x$. Incomparable codes
cannot have the same chain, so this is a proper coloring of $\Gamma_v$.
It proves the first bound in (CL.21) and $A\ge\tau(\chi_v)$.
Repeated codes at nonadjacent vertices and isolated vertices cause no
problem; no injectivity of the coordinate codes is assumed.

Proof of the cut bound. By (CL.9), each actual support has the form
$U_j=T_a\cup R_j$ with $R_j\subseteq X_B$ and $|R_j|=t_v$.
Each demanded edge has to be cut by at least two distinct supports:
one for each of its opposite membership orientations. A single support
cuts at most $M_v$ edges. Finite incidence counting gives

$$
2|E(\Gamma_v)|
\le\sum_{j=1}^A|\{e\in E(\Gamma_v):|e\cap R_j|=1\}|
\le A M_v.
\tag{CL.23}
$$

For a graph with an edge, division by positive $M_v$ and integrality
give the ceiling in (CL.19). For an edgeless graph, $A\ge1$ suffices.
Finally (CL.5) gives $b_v\ge a_v$. The chain decomposition, coloring,
and incidence count are standard combinatorial tools; their inputs here
are the actual supports supplied by the join theorem. $\square$

**Corollary 5.2 (nonbipartite demands require two excess incidences).**
If $\Gamma_v$ is nonbipartite, then $a_v\ge3$ and $e_v=b_v-1\ge2$.
Indeed $A=1$ permits at most one color and $A=2$ at most
$\binom21=2$ colors in (CL.21), contradicting nonbipartiteness.
An odd cycle is sufficient: a two-coloring would alternate around it
and fail on the closing edge. This is a conditional consequence, not
an assertion that any original pool must have an odd cycle.

All witnesses at $v$ are combined in $\Gamma_v$ before applying these
bounds. Duplicate demands get no extra charge. Overlapping odd cycles
are not summed independently, and neither are the chromatic and cut
bounds: they combine by the maximum in (CL.19). No positive lower
degree or absence of isolated coordinates is required.

## 6. Pool demand capacity without double counting the baseline

For each internal depth $d$ define

$$
\Lambda_d=\sum_{v\in V_d}(\kappa_v-1),\qquad
P_B=\sum_{d=a+1}^{b-1}\max(1,\Lambda_d),\qquad
\Delta_B=P_B-(\beta_B-1).
\tag{CL.24}
$$

When $\beta_B=1$, all these depth sums are empty, $P_B=\Delta_B=0$.
Otherwise $\Delta_B\ge0$.

**Theorem 6.1 (quantitative pool excess).** Every consecutive gap,
of arbitrary span in every original graph, satisfies

$$
\begin{aligned}
E_B&\ge P_B=(\beta_B-1)+\Delta_B,\\
D_B-E_B&\le D_B-(\beta_B-1)-\Delta_B,\\
|Q_B|&\ge|V_B|+(\beta_B-1)+\Delta_B-D_B.
\end{aligned}
\tag{CL.25}
$$

If some $\Gamma_v$ is nonbipartite, then $\Delta_B\ge1$.

Proof. Theorem 5.1 gives $e_v\ge\kappa_v-1$. Summing on one
diagonal gives $e_d\ge\Lambda_d$. Independently its noncommonness
gives $e_d\ge1$ by (CL.12). Thus
$e_d\ge\max(1,\Lambda_d)$. Sum over the disjoint internal diagonals
for the first assertion; subtract it from $D_B$ for the second and
use (CL.10) for the third. If a demand graph is nonbipartite,
Corollary 5.2 and (CL.19) give $\kappa_v\ge3$, so that depth has
$\Lambda_d\ge2$. One summand exceeds its baseline one by at least
one, proving $\Delta_B\ge1$. All statements also hold for an empty
interior. $\square$

The baseline and the demand requirement combine by a maximum at each
depth; adding them would allocate the same excess twice. Distinct cells
are summed only as their actual excess incidences $b_p-1$. Sharing
between cells still contributes to $D_B$. Excess incidences are not
silently converted into distinct installed states.

## 7. Credited signs for the other pools

The global application uses the compensated spans and early endpoints
of SI Sections 9–10. Their finite proofs are given here to fix exactly
the signs used. They are credited background, separate from the union,
join and demand bounds.

**Lemma 7.1 (last-layer exclusivity and early endpoints).** A host at
depth $b-1$ cannot host another count cell in $V_B$. If
$b\le\max(K,L)$, then $D_B=0$.

Proof. At depth $b-1$, (CL.9) implies
$S=T_b\setminus\{i(q)\}$. Every other live occurrence of $q$ in
the pool has support contained in that set, because its label is fresh.
At an earlier depth it is a proper subset; at the same depth it is
equal. Nested-support and equal-support/unequal-hit exclusions give
the first assertion. It also holds for $b=n$.

For the second assertion use (CL.14): a shared pair would require
$r,s\ge n-b+1\ge\min(K,L)$. One of the hit or zero ranges has
diameter $\min(K,L)-1$, making this impossible. This recovers the
early-endpoint consequence of SI Lemma 10.2 using the stronger union
bound. $\square$

**Lemma 7.2 (spans at most three; SI Theorem 9.4).** If $\beta_B\le3$,
then $D_B\le E_B$.

Proof. Span one has empty interior. For span two, write
$X_B=\{x,y\}$. An interior support is $T_a$ plus one of these
coordinates; its next fixed label must be the other. Different supports
therefore cannot share a state; equal supports at different cells are
also excluded. Hence $D_B=0$.

For span three, the last internal layer $a+2$ is exclusive by Lemma
7.1. A support at $a+1$ and one at $a+2$ are either nested or have
union $T_b$. In the latter case no label in $T_b$ is fresh for both,
so cross-depth sharing is impossible too. All sharing is at $d=a+1$.
For a cell let $\mathcal L(p)$ be its set of live replies. These sets
are nonempty at this depth. If two hosted cells had a common live
reply, their fixed successor would share two distinct last-layer cells,
which is impossible. Thus a shared state has exactly two cells with
opposite singleton live-reply sets. They can only be

$$
(d-L+1,L-1),\qquad(K-1,d-K+1).
\tag{CL.26}
$$

Invalid cells or pairs failing (CL.3) are omitted. Let $s$ be the
number of such shared states. Then $D_B=s$. If $s\ge2$, these two
cells have at least $s$ hosts each, so their excess is at least
$2s-2\ge s$. If $s=1$, depth $d$ is noncommon and (CL.12) gives
excess at least one. If $s=0$ there is no deficit. In every case
$E_B\ge D_B$. Only actual live children were constrained.
$\square$

**Lemma 7.3 (span four; SI Lemma 10.3 and Theorem 10.4).** If
$\beta_B=4$, then $D_B\le E_B$.

Proof. Put $d=a+1$, $\alpha=d-L+1$, $\beta=K-1$, and label the
following formal cells:

$$
\begin{array}{lll}
A=(\alpha,L-1),& C=(\alpha+1,L-2),&
Y=(K-2,d-K+2),\\
Z=(K-1,d-K+1),& U=(\alpha+1,L-1),&
V'=(K-1,d-K+2).
\end{array}
\tag{CL.27}
$$

The first four have depth $d$, the last two depth $d+1$. Omit invalid
cells, coincident endpoints and pairs failing (CL.3). The last layer
$d+2$ is exclusive. At depth $d+1$, a common live reply at a shared
state would share two last-layer cells, so the only possible pair has
opposite singleton live replies, namely $UV'$. Between depths $d$
and $d+1$ the same reasoning forces opposite singleton live replies,
giving only $AV'$ and $ZU$.

For two shared cells at depth $d$, no common live reply gives $AZ$.
A common zero reply must give $UV'$ at the successor; subtracting
$(0,1)$ gives $CZ$. A common one reply similarly gives $AY$.
Thus all possible pairs are

$$
AZ,\quad CZ,\quad AY,\quad UV',\quad AV',\quad ZU.
\tag{CL.28}
$$

Every $CZ$ host has its actual zero successor at a shared $UV'$ host;
every $AY$ host has its actual one successor there. No injectivity of
these successor maps is asserted.

No host has three cells. Indeed $H=\beta-\alpha=n-1-d\ge2$.
If $H=2$, (CL.3) deletes every pair except $AZ$. If $H\ge3$, the
six formal cells are distinct and the depth-$d$ pairs form the path
$C-Z-A-Y$, with no triangle. The two depth-$d+1$ cells have opposite
singleton live replies. A mixed triple containing both would require
an earlier cell with a nonempty live-reply set disjoint from both,
which is impossible. A mixed triple with two earlier cells would
require both to have the same specified singleton live-reply set;
there is at most one such cell at a given depth. Boundary deletions
cannot introduce a triple. This proves that every shared host has
exactly two incidences.

Let $s$ be the number of shared hosts, so $D_B=s$. Regard them as a
multigraph on the cells in (CL.27), with one edge per distinct state.
This multigraph is an incidence device, distinct from the simple
coordinate-demand graph $\Gamma_v$. Let $v_0\le6$ be its number of
incident cells. A cell's host count is at least its degree. Every
internal layer is noncommon, so writing their excesses as $e_1,e_2,e_3$
gives $e_j\ge1$. The last layer has no incident cell, and hence

$$
E_B\ge3,\qquad E_B\ge2s-v_0+1\ge2s-5.
\tag{CL.29}
$$

This uses no positive degree assumption for a cell outside the edge
relation. If $E_B<s$, these integer inequalities force $s=4,E_B=3$
and then $v_0=6$. All six cells must therefore be distinct and valid;
any missing or identified boundary cell has already made a deficit
impossible. Also $e_1=e_2=e_3=1$. The incident cells have exactly
their degree many hosts, and every other cell of the first two layers
has one host, since equality holds in the incidence bound.

Let $x,y,z_0,u_0,v_1,w_1$ be the edge multiplicities of
$CZ,AY,UV',AZ,AV',ZU$. The pendant cells $C,Y$ give $x,y\ge1$;
their successor obligations give $z_0\ge1$. Counting all edges and
degrees on the two layers yields

$$
\begin{aligned}
x+y+z_0+u_0+v_1+w_1&=4,\\
2x+2y+2u_0+v_1+w_1-4&=1,\\
2z_0+v_1+w_1-2&=1.
\end{aligned}
\tag{CL.30}
$$

Thus $z_0=1$, $v_1+w_1=1$, $x=y=1$ and $u_0=0$.
If $v_1=1$, only $A$ on the first layer has more than one host.
All cells from $C$ through $Z$ have singleton support families;
the adjacent-child argument of Section 2 makes those supports equal.
Their shared $CZ$ host contradicts equal-support/unequal-hit exclusion.
If $w_1=1$, the same argument from $A$ through $Y$ contradicts
their shared $AY$ host. Both possibilities are excluded, proving
$D_B\le E_B$. No certified edge or continuation was constrained.
$\square$

## 8. Same-graph collective consequence and the residual target

Partition the consecutive gaps as

$$
\mathcal L_*=\{B=(a,b):\beta_B\ge5,\ b>\max(K,L)\},\qquad
\mathcal A_*=\mathcal B\setminus\mathcal L_*,
$$

and put

$$
R=E_{\rm cut}+u+\sum_{B\in\mathcal A_*}(E_B-D_B)\ge0.
\tag{CL.31}
$$

The sign follows from Lemmas 7.1–7.3 and the nonnegativity of cut
excess and $u$. These are the precise credited signs used in SI.59.

**Theorem 8.1 (collective demand restriction).** On the one original
complete graph,

$$
\begin{aligned}
\sum_{B\in\mathcal L_*}(D_B-E_B)
&\le\sum_{B\in\mathcal L_*}
       \bigl(D_B-(\beta_B-1)-\Delta_B\bigr),\\
m-G&\ge R-\sum_{B\in\mathcal L_*}
       \bigl(D_B-(\beta_B-1)-\Delta_B\bigr).
\end{aligned}
\tag{CL.32}
$$

In particular $m<G$ requires

$$
\sum_{B\in\mathcal L_*}
\bigl(D_B-(\beta_B-1)-\Delta_B\bigr)>R.
\tag{CL.33}
$$

Proof. Sum the deficit bound (CL.25) over the late-long pools. Their
cell sets are disjoint, so the bounds use disjoint summands of $E$.
The exact identity (CL.10) is
$m-G=R-\sum_{B\in\mathcal L_*}(D_B-E_B)$, giving (CL.32).
If $m<G$, that exact deficit exceeds $R$, so its upper bound also
exceeds $R$. Cut states and other pools have their original single
locations. Certified traffic that is live elsewhere stays in its live
pool; only genuinely never-live states enter $u$. $\square$

This is a necessary restriction on any strict-subgrid graph. It is not
a sufficient criterion for correctness, termination or either resource
cap. No demand graph is assumed nonbipartite, and no claim is made that
$\Delta_B>0$ in every deficient pool. Sharing can fail (CL.15), or its
eligible private demands can form only bipartite or edgeless graphs.
Both cases remain within the theorem's scope.

To state the exact remaining obligation, put
$R_B^{\rm rem}=E_B-P_B\ge0$. Then (CL.10) rewrites the original
comparison $m\ge G$ as

$$
\sum_{B\in\mathcal L_*}
\bigl(D_B-(\beta_B-1)-\Delta_B-R_B^{\rm rem}\bigr)\le R.
\tag{CL.34}
$$

This residual formula is bookkeeping from the credited identity, not
another new bound. The demand theorems do not control the remaining
duplicate incidences by $R_B^{\rm rem}$, cut excess, genuine nonlive
states or other-pool surplus strongly enough to prove (CL.34).
Independent lower bounds for different prefixes or overlapping coordinate
sets cannot be subtracted to create additional states. Requiring every
long pool to compensate separately would also be stronger than this
collective target.

For the original all-size domain $\min(k,n-k+1)\ge4$, the alternatives
remain unresolved: either prove collective compensation for every
complete original graph at both $n,W$ caps, or give one complete correct
strict-subgrid graph meeting both caps on every input. No such graph
is constructed here. The credited SI Open problem 14.6 interval at
$n=8,k=4$ remains $17\le m_{\rm exec}\le20$ as supplied background;
these inequalities assert no improved universal numerical optimum.
No critical-twenty equality argument is needed as a premise. The
unrestricted-budget minimum is a separate question.

## 9. Original full-fiber native consumer

The native interpretation uses only the conditional correspondence
SI.5. In this section $r\ge0$ is the original additional-latch parameter.
Its source is the entire unbounded fiber

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\quad \rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle v,w\rangle=\langle\rho v,\rho w\rangle,
\qquad
\mathcal U_*=\{u:R_{\{L,R\}^3}(\rho u)=R_*\}.
\tag{CL.35}
$$

There is no size, depth or interior-shape restriction on these finite
nonempty ordered trees. The complete current row has classes
$\{LLL,LRL\}=a$, $\{LLR\}=b_1$, $\{LRR\}=b_2$,
$\{RLL,RRL\}=c$, $\{RLR\}=b_3$, $\{RRR\}=b_4$,
with different classes disequal. At the original literals
$w_i=L^{s_i}R$, $a_i=LLLw_i$, define
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$; alpha, beta
and absent each contribute zero. Retain the original eleven profiles
and the literal pointwise code

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ in another zero profile}.
\end{cases}
\tag{CL.36}
$$

Preparation must return the original latch $\widehat e_{\sigma_{A,k}(u)}$,
and code-only handoff must enter literally the original complete
$e_{\sigma_{A,k}(u)}$ on that same source. The supplied interface is

$$
\mathsf N_{A,k,r}(H,p,\ell)
\quad\Longleftrightarrow\quad
\mathsf B_{c,k}(H-4-r,p-1,\ell-3).
\tag{CL.37}
$$

In its projection direction a correct full-fiber native preparer with
both caps $n+1,W+3$ has one actual Boolean projection with both
$n,W$ caps and $m\le H_P-4-r$. Apply the preceding results to that
particular graph, without separately selecting or optimizing residual
graphs. For example (CL.32) gives the conditional data-dependent bound

$$
H_P\ge G+4+r+R-
\sum_{B\in\mathcal L_*}
\bigl(D_B-(\beta_B-1)-\Delta_B\bigr),
\tag{CL.38}
$$

where every quantity on the right is from that one supplied projection.
Indeed $H_P\ge m+4+r$, and (CL.32) bounds that same $m$. No
independent native lower-bound or source-realization bridge is being
asserted.

For clarity the supplied lift leaves a Boolean graph unchanged at
the original fixed literals. At each coordinate-$i$ row, its four
fixed successors are installed separately as

$$
(\mathsf{alpha},\mathsf{beta},\mathsf{branch},\mathsf{absent})
\longmapsto(\delta_0,\delta_0,\delta_1,\delta_0),
\tag{CL.39}
$$

with terminals replaced by the original latches. Its original paid
profile front is

| State | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | Boolean start | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

Together with all $r$ additional mandated latches, this counts
$m+4+r$ preparation states: $m$ running rows, two profile rows and
$2+r$ latches. The Boolean terminals are replaced, not charged a
second time. The all-address occurrence identity in SI.5 makes each
$Z_{b_3}$ source's selected route an actual Boolean run on its one
fixed indicator vector, including noncomb images, absent selected
addresses, repeats and certified visits. Its profile front adds one
call and three letters. Other profiles use at most two calls and six
letters. This is the stated full-fiber supplier, not a new proof of
its source homomorphism or profile classification. The lower projection
uses actual cube witnesses and selected-state subsequences; it is not
a restriction of the upper's full source domain or a read-once
normalization.

The independent original whole-row reader has three running states and
five whole-row halts, eight separately priced states, and at most two
fresh calls and six fresh letters. It returns the entire predecessor
row, including ordered exterior, occurrences, canonical equality
partition, repetitions, disequalities and strict-prefix guards. All
finite original addresses and alpha, beta, branch and absent replies
retain their meaning and permission. Every installed output, running,
unused and latch state and every actual constant, repeated or
postcertificate invocation keeps its charge.

Source binding, the fixed register, acquired same-version row,
authentication, permission, export, access isolation, code-only handoff,
lawful complete entry and stationary service remain the separate
supplied assumptions of SI Convention 1.3 and WTF Assumption 1.5.
No acquired source, free history, archive reread, clock, address
computation or extra work register follows. Installed control,
table and address representation, retained export alphabet, workspace,
acquisition, elapsed time and physical memory remain distinct
quantities. These conditional finite-control bounds assert no physical
resource or realization law.

## 10. Attribution and mathematical boundary

SI owns the original model and native interface, live freshness and
support exclusions, actual fixed successors, singleton diagonal
argument, common-support envelopes and localization, exact incidence
identities, right-cut separation and span-at-most-four compensation.
Its all-history both-conflict capacity, exact count relaxation,
star and cyclic injections, and complete above-grid inclusions remain
credited prior results. Neither a proper-order class nor an above-grid
inclusion is offered as additional progress on the unrestricted target.

The supplied common-cone mathematical projection gives the union,
actual private-join and combined demand-capacity route developed here.
Its additional model-specific deductions are (CL.13) for every hosted
subcollection, (CL.16) from separately actual fixed-successor
continuations, and the joint use of actual membership and fixed-size
cuts in (CL.20)–(CL.25). These yield a quantitative limit on reuse of
forced separations on one graph, including arbitrary long pools.
Symmetric-chain decomposition of the Boolean lattice, chromatic
coloring, inclusion-exclusion and finite incidence counting are
standard combinatorial tools, not original discoveries. Rewriting the
exact remaining target as (CL.34) is also not new mathematical content.

These are ordinary symbolic deductions conditional on the displayed
SI interfaces. No external unrestricted branching-program lower bound,
new axiom, kernel verification, independent review, numerical or
exhaustive search, empirical learning, general neural-network claim,
worldwide priority or completion of the continuing research programme
is asserted. The unresolved obligation is enough same-graph compensation
for all remaining duplicate incidences, or a complete correct original
strict-subgrid realization at both original whole-run caps.

## 追加锚（本行以下为增补区）

## 11. Propagation of all actual supports at a cell

Retain the entire graph, source interfaces and notation of Sections 1–10.
In particular both bounds (CL.2) hold on every complete actual run of
this one stationary graph. Fix a consecutive gap $B=(a,b)$ and write
$d(v)=h(v)+z(v)$ for the depth of a cell. Every support family below
is the entire actual family at that cell, rather than a selection of
representatives or the supports inherited from just one parent.

For $v\in V_B$ put

$$
U_v=\bigcup_{S\in\mathcal S_v}S,\qquad
\rho_v=|U_v|-d(v),\qquad
\nu_v=|\{x\in X_B:\deg_{\Gamma_v}(x)>0\}|.
\tag{CL.40}
$$

Thus $\nu_v$ counts only coordinates incident to a demand edge; isolated
coordinates are still vertices of $\Gamma_v$. It is distinct from the
number $u$ of genuinely never-live installed states. All these finite
sets describe actual histories and provide no history store or selector.

**Theorem 11.1 (actual descent of every alternative support).** Let
$v\in V_B$, $d=d(v)$ and $A=a_v$. If

$$
w=v+(j_1,j_0)\in V_B,\qquad
j_1,j_0\ge0,\qquad j=j_1+j_0,
$$

then every $S\in\mathcal S_v$ is contained in some member of
$\mathcal S_w$. Consequently

$$
a_w=1\quad\Longrightarrow\quad
|U_v|\le d+j,\qquad \rho_v\le j,\qquad \nu_v\le j a_v.
\tag{CL.41}
$$

One has $0\le\rho_v\le b-d$. Either $j<\rho_v$ or
$\nu_v>j a_v$ therefore forces $a_w\ge2$ and $e_w\ge1$.
In particular, if either strict inequality holds, then

$$
e_{d+j}\ge
|\{w\in V_B:w=v+(j_1,j_0),\ j_1,j_0\ge0,\ j_1+j_0=j\}|.
\tag{CL.42}
$$

Proof. For each support $S$ choose one actual history at $v$ with that
support. Append a reply word having $j_1$ ones and $j_0$ zeros. Its
partial counts are bounded coordinatewise by the final live counts of
$w$, so every prefix stays live. Repeated use of (CL.6) gives an actual
extension, with fresh queries, whose final support contains $S$.
Each extension is realized on a completion of its own exposed assignment.
Different starting supports need no common completing input and need
not follow the same coordinate sequence.

If $\mathcal S_w=\{T\}$, each of these final supports is $T$.
Thus $S\subseteq T$ for every $S\in\mathcal S_v$, and
$U_v\subseteq T$ with $|T|=d+j$. This proves the first two necessary
inequalities in (CL.41). The envelope (CL.9) puts $U_v$ inside $T_b$,
while the nonempty family contains a set of size $d$; hence
$0\le\rho_v\le b-d$.

If $x$ is incident to a demanded edge, Theorem 4.1 supplies a support
at $v$ containing $x$ and a support at $v$ omitting $x$, by the two
opposite membership orientations. Under the singleton premise every
such $x$ lies in $T$ and belongs to $T\setminus S$ for at least one
$S\in\mathcal S_v$. Since each $S$ has size $d$ and is contained
in $T$, finite union counting gives

$$
\nu_v\le\left|\bigcup_{S\in\mathcal S_v}(T\setminus S)\right|
       \le\sum_{S\in\mathcal S_v}|T\setminus S|=a_v j.
\tag{CL.43}
$$

This proves the last necessary inequality. Their contrapositives and
(CL.5) give the ambiguity and excess conclusions. Each distinct forced
cell contributes a different summand $e_w\ge1$ to its depth sum,
proving (CL.42). Its hosts are not declared disjoint; any sharing is
still retained in $D_B$. When $j=0$, the singleton premise gives
$\rho_v=\nu_v=0$. When the displayed descendant set is empty, (CL.42)
is the zero lower bound. No positive range is inferred from
$\rho_v=0$. $\square$

The union in Theorem 3.1 concerns different count cells at one shared
host. The union $U_v$ instead concerns all alternative supports at one
cell, including supports at different hosts. These are different
constraints on the same actual graph.

**Lemma 11.2 (a demanded cell has two internal live children).** If
$\Gamma_v$ contains an edge, both $v_0=(g,z+1)$ and $v_1=(g+1,z)$,
where $v=(g,z)$, are distinct live cells in $V_B$.

Proof. An edge has an eligible witness from Section 5. For its gaps
$r,s$ put $\ell=n-b$. By (CL.14)–(CL.15),

$$
r,s\ge\max(2,\ell+1),\qquad g+r\le K,\quad z+s\le L.
\tag{CL.44}
$$

Thus $g\le K-2,z\le L-2$, so both children are live. Furthermore
$d(v)=g+z\le n+1-r-s$. If $\ell=0$, this is at most
$n-3=b-3$. If $\ell\ge1$, it is at most
$n-2\ell-1=b-\ell-1\le b-2$. In both cases $d(v)+1<b$.
Their depths are above $a$ because $v$ is interior. This also covers
the formal endpoint $b=n$. No such conclusion is asserted merely from
an edgeless demand graph. $\square$

## 12. A correction across disjoint adjacent depth pairs

Keep the combined chromatic and fixed-size cut bound $\kappa_v$ of
(CL.19) in full. For each internal depth name its existing lower bound

$$
p_d=\max(1,\Lambda_d),\qquad
\Lambda_d=\sum_{v\in V_d}(\kappa_v-1),\qquad
P_B=\sum_{a<d<b}p_d=(\beta_B-1)+\Delta_B.
\tag{CL.45}
$$

These are exactly the quantities of (CL.24), with $p_d$ naming its
summand. An edge-containing graph has $\chi_v\ge2$ and
$\tau(\chi_v)\ge2$, so $\kappa_v\ge2$. Thus $\kappa_v=1$ is
equivalent to $\Gamma_v$ being edgeless under the original convention.

**Theorem 12.1 (host saturation or ambiguity in both children).**
If $\nu_v>\kappa_v$, then

$$
e_v\ge\kappa_v
\quad\hbox{or}\quad
a_{v_0}\ge2\ \hbox{and}\ a_{v_1}\ge2.
\tag{CL.46}
$$

In particular $b_v=\kappa_v$ forces the second alternative. For either
child $w$ whose demand graph is edgeless,

$$
\bigl(e_v-(\kappa_v-1)\bigr)+e_w\ge1.
\tag{CL.47}
$$

Proof. The premise cannot hold for an edgeless graph, where
$\nu_v=0,\kappa_v=1$. Both children are therefore live and internal
by Lemma 11.2. Capacity (CL.20) gives $b_v\ge a_v\ge\kappa_v$.
If the first alternative fails, integrality gives
$b_v=a_v=\kappa_v$. Apply (CL.41) with $j=1$ separately to the two
children: $\nu_v>a_v$ forbids a singleton support family at either.
This proves (CL.46). In its first alternative the parent difference in
(CL.47) is at least one; if that difference is zero, both children have
$e_w\ge1$. The difference and all other excess terms are nonnegative,
which proves (CL.47). No separate charge is assigned to an edge witness.
$\square$

**Theorem 12.2 (one further unit on adjacent depths).** If a cell
$v\in V_d$ satisfies $\nu_v>\kappa_v$ and at least one of its children
has $\kappa=1$, then $a<d<d+1<b$ and

$$
e_d+e_{d+1}\ge p_d+p_{d+1}+1.
\tag{CL.48}
$$

Proof. Lemma 11.2 gives the two internal children. Since
$\kappa_v\ge2$, one has $\Lambda_d\ge1$ and $p_d=\Lambda_d$.
If $e_v\ge\kappa_v$, sum all other credited cell bounds
$e_x\ge\kappa_x-1$ on depth $d$ to obtain
$e_d\ge\Lambda_d+1=p_d+1$. Combine it with $e_{d+1}\ge p_{d+1}$.

Otherwise Theorem 12.1 gives $e_{v_0},e_{v_1}\ge1$. If
$\Lambda_{d+1}\ge1$, a child with $\kappa=1$ contributes one above
its credited bound zero; all other cell bounds still give
$e_{d+1}\ge\Lambda_{d+1}+1=p_{d+1}+1$. If
$\Lambda_{d+1}=0$, both distinct children have credited bound zero,
and together give $e_{d+1}\ge2=p_{d+1}+1$. In either case combine
with $e_d\ge p_d$. The extra unit is above the existing maximum
baseline, rather than an additional copy of it. $\square$

Let $\mathcal T_B$ be the set of depths satisfying the trigger of
Theorem 12.2 for at least one cell. Define

$$
\mu_B=\max\left\{|\mathcal M|:
 \mathcal M\subseteq\mathcal T_B,\quad
 \{d,d+1\}\cap\{d',d'+1\}=\varnothing
 \text{ for distinct }d,d'\in\mathcal M\right\}.
\tag{CL.49}
$$

The empty choice is permitted, with size zero. This is a finite
mathematical index of this graph, not an executed optimization or a
resource available during a run. Several triggering cells, edges or
witnesses at one depth still give only that one depth pair.

**Theorem 12.3 (disjoint-depth pool correction).** Every consecutive
gap of every original graph satisfies

$$
\begin{aligned}
E_B&\ge P_B+\mu_B=(\beta_B-1)+\Delta_B+\mu_B,\\
D_B-E_B&\le D_B-(\beta_B-1)-\Delta_B-\mu_B,\\
|Q_B|&\ge |V_B|+(\beta_B-1)+\Delta_B+\mu_B-D_B.
\end{aligned}
\tag{CL.50}
$$

Proof. Choose a largest subfamily in (CL.49). Apply (CL.48) to each
of its pairs, and apply $e_d\ge p_d$ to every internal depth outside
those pairs. Each depth occurs exactly once in the resulting sum.
Thus $E_B\ge\sum_{a<d<b}p_d+\mu_B=P_B+\mu_B$.
Subtract from $D_B$ for the second line and use (CL.10) for the third.
The host and support data, including every duplicate incidence, are
from the unchanged graph. No edge, witness, baseline or overlapping
depth is charged twice.

An empty interior has $P_B=\Delta_B=\mu_B=0$. An empty trigger set,
or the absence of an internal adjacent pair, gives $\mu_B=0$ and
recovers (CL.25). Isolated demand coordinates contribute nothing to
$\nu_v$. These conventions include the last internal layer and all
boundary deletions without inserting a fictitious child. $\square$

**Corollary 12.4 (two distinct edges obstruct the old baseline).**
If $\Delta_B=0$ and some $\Gamma_v$ has at least two distinct edges,
then

$$
\mu_B\ge1,\qquad E_B\ge\beta_B.
\tag{CL.51}
$$

In particular $E_B=\beta_B-1$ is impossible under this trigger,
including for bipartite demand graphs.

Proof. Each $p_d\ge1$, so $\Delta_B=0$ forces every $p_d=1$ and
$\Lambda_d\le1$. At the specified cell an edge gives
$\kappa_v\ge2$, and $\Lambda_{d(v)}\le1$ forces $\kappa_v=2$.
Two distinct edges of a simple graph have at least three incident
vertices. Thus $\nu_v\ge3>\kappa_v$. Its children are distinct and
internal by Lemma 11.2. They cannot both have $\kappa\ge2$, which
would give $\Lambda_{d(v)+1}\ge2$. At least one has $\kappa=1$,
so this depth belongs to $\mathcal T_B$ and $\mu_B\ge1$.
Now $P_B=\beta_B-1$ and (CL.50) prove (CL.51). No odd cycle is
required. A single simple edge has $\nu_v=\kappa_v=2$: a size-$t_v$
cut can cut it, so $M_v=1$, while both terms of (CL.19) equal two.
It therefore supplies no $\nu_v>\kappa_v$ trigger by itself.
$\square$

## 13. Exact-baseline rigidity and its host justification

**Theorem 13.1 (necessary local coordinate swap at the exact baseline).**
Suppose $E_B=\beta_B-1$. On every internal depth there is exactly one
support-ambiguous cell. At that cell $b_v=a_v=2$, while every other
cell on the depth has $b_v=a_v=1$. Every support at every interior
cell has exactly one host.

If the ambiguous cell $v$ has two live internal children, its two
supports $S_1,S_2$ satisfy

$$
S_1\setminus S_2=\{x\},\qquad
S_2\setminus S_1=\{y\},\qquad x\ne y.
\tag{CL.52}
$$

Writing $q_1,q_2$ for their unique respective hosts, one has

$$
i(q_1)=y,\quad i(q_2)=x,\qquad
\delta(q_1,0)=\delta(q_2,0),\quad
\delta(q_1,1)=\delta(q_2,1),
\tag{CL.53}
$$

and the zero and one successor states are distinct. The inherited
support in either child is $S_1\cup S_2$. The entire child family
can have an additional support from another parent. Every demand
graph $\Gamma_v$ in this gap is edgeless or has just one edge.
These are necessary conditions, not a complete graph specification.

Proof. There are $\beta_B-1$ internal depths. Their nonnegative
integer excesses satisfy $e_d\ge1$ by (CL.12), so equality of their
sum forces every $e_d=1$. Noncommonness supplies a cell with
$a_v\ge2$ on each such depth. Since $b_v\ge a_v$, that cell uses
the entire unit of excess and has $b_v=a_v=2$; every other cell
has $b=a=1$. The fixed-cell map from hosts onto supports described
in (CL.5) is a surjection of finite sets of equal sizes at every
interior cell. It is consequently a bijection: each support has
exactly one host. This is stronger than merely knowing $a_v\le2$.

Now let $d=d(v)$ and let both children be live and internal. If
$|S_1\cup S_2|\ge d+2$, then $\rho_v\ge2$. Theorem 11.1 with
$j=1$ forces both children ambiguous. Their two positive excesses
contradict $e_{d+1}=1$. Distinct $d$-element supports have union of
size at least $d+1$, so their union has exactly that size. This
proves (CL.52).

Set $Z_i=S_i\cup\{i(q_i)\}$ for $i=1,2$. By (CL.6), each $Z_i$
is an actual support at each of the two children. If $Z_1\ne Z_2$,
both children are again ambiguous, contradicting $e_{d+1}=1$.
Thus $Z_1=Z_2$. It contains $S_1\cup S_2$, and all these sets
have size $d+1$, so it equals that union. Freshness now forces
the queried coordinates in (CL.53). For a fixed reply the two
successors host the same inherited support in the same child cell.
The already proved host–support bijection at that child, not a
singleton-family assumption, identifies those successors. The zero
and one child cells have unequal hits and the same inherited
support; the equal-support exclusion in Section 1 forbids a common
host between them. Their successor states are therefore distinct.
Another parent may supply a second support at the sole ambiguous
child on that depth, consistently with all these conclusions.

A demanded cell has at least two supports by Theorem 5.1, hence is
the sole ambiguous cell on its depth. Lemma 11.2 gives its two live
internal children, so (CL.52) applies there. Among its two supports
only $x,y$ have varying membership, and their membership orientations
are opposite. Every other coordinate is present in both supports or
in neither. An edge requires both opposite membership orientations
by Theorem 4.1, so its only possible pair is $\{x,y\}$. A cell
with one support has no demand edge. This proves the final assertion.

For an empty interior the depth assertions are vacuous. An ambiguous
cell with only one live child, or in the last internal layer, is
outside the two-child assertion. No unproved singleton property is
assigned to its descendants, and no paid certified continuation is
removed. $\square$

## 14. Tight common-cone capacity as an uncharged diagnostic

**Proposition 14.1 (exhausted complement and private AND/OR arms).**
Consider a shared pair from Corollary 3.2, with supports $S,T$ at
$p=(h,z),p'=(g,w)$ and gaps $r=g-h,s=z-w$. Put $\ell=n-b$.
Suppose the common-cone bound is tight:

$$
|S\cup T|=g+z-\ell.
$$

Set

$$
C=T_b\setminus(S\cup T),\quad N=n-g-z,\quad
A_1=K-1-g,\quad A_0=L-1-z.
\tag{CL.54}
$$

For every reply word with $A_1$ ones and $A_0$ zeros, the $N$ common
available queries, including the query after its last reply, form a
permutation of $C$. At that final shared state, the zero successor
has a live occurrence extending the higher-hit history and queries
a coordinate in $S\setminus T$. The one successor has a live
occurrence extending the lower-hit history and queries a coordinate
in $T\setminus S$. These two successor states are distinct. The
surviving lower and higher contexts have residual predicates

$$
\operatorname{AND}\bigl((T\setminus S)\cup([n]\setminus T_b)\bigr),
\qquad
\operatorname{OR}\bigl((S\setminus T)\cup([n]\setminus T_b)\bigr),
\tag{CL.55}
$$

respectively. These predicates describe those actual contexts, not
a context-independent residual attached to an installed state.

Proof. Tightness gives $|C|=N=A_1+A_0+1\ge1$. Every prefix of a
word with the specified counts is live for both histories. The proof
of Theorem 3.1 works for any such word: its fixed-successor induction
uses only these partial count bounds. It gives $N$ distinct common
available coordinates in $C$. Since $|C|=N$, these exhaust $C$.
No agreement of the original exposed assignments is required.

After all $N-1$ replies and before the last query, the lower and
higher counts are, respectively,

$$
(K-1-r,L-1),\qquad(K-1,L-1-s).
\tag{CL.56}
$$

A one reply leaves the lower context live at $(K-r,L-1)$ and
certifies the higher. A zero reply leaves the higher context live
at $(K-1,L-s)$ and certifies the lower. The gaps $r,s\ge2$
guarantee the asserted surviving liveness. After that reply the
surviving supports are respectively $S\cup C$ and $T\cup C$.
Their depths are $n-r$ and $n-s$, both at most $b-1$ by
$r,s\ge\ell+1$ in (CL.14), and both remain above $a$.
The envelope and freshness therefore put their next fixed labels in

$$
T_b\setminus(S\cup C)=T\setminus S,\qquad
T_b\setminus(T\cup C)=S\setminus T,
\tag{CL.57}
$$

respectively. These private sets are nonempty and disjoint, so the
successor states are distinct.

Tightness also gives $|T\setminus S|=r-\ell$ and
$|S\setminus T|=s-\ell$. Exactly $r$ coordinates remain unread in
the surviving lower context, and its $K-r$ old ones require all
$r$ to be one. Exactly $s$ remain unread in the surviving higher
context, and its $K-1$ old ones require at least one more. Their
unread sets are precisely those displayed in (CL.55), proving the
predicates. This covers $N=1$, $b=n$ and unequal original depths.
$\square$

The proposition locates two arms in existing live pools. It does not
show that either arm supplies an additional installed host or a
never-live state. Different words and witnesses may reuse states.
The certified occurrence still follows the same fixed successor and
pays every subsequent visit. This diagnostic contributes no separate
term to $\mu_B$, $E_B$ or a global compensation sum.

## 15. Collective consequence on the unchanged graph

Keep $\mathcal L_*,\mathcal A_*$ and the same-graph reserve $R\ge0$
of (CL.31). Every quantity below, including the correction $\mu_B$,
is computed as a mathematical index of that one original table.

**Theorem 15.1 (collective restriction with propagation correction).**
One has

$$
\begin{aligned}
\sum_{B\in\mathcal L_*}(D_B-E_B)
&\le\sum_{B\in\mathcal L_*}(D_B-P_B-\mu_B),\\
m-G&\ge R-\sum_{B\in\mathcal L_*}
 \bigl(D_B-(\beta_B-1)-\Delta_B-\mu_B\bigr).
\end{aligned}
\tag{CL.58}
$$

Thus $m<G$ requires

$$
\sum_{B\in\mathcal L_*}
 \bigl(D_B-(\beta_B-1)-\Delta_B-\mu_B\bigr)>R.
\tag{CL.59}
$$

Proof. Sum (CL.50) over the disjoint late-long pools. Within each
pool (CL.49) has already made every selected adjacent depth set
disjoint, and the remaining depths supply their original $p_d$ once.
Localization in Lemma 2.2 separates different pools and cuts. The exact
identity remains
$m-G=R-\sum_{B\in\mathcal L_*}(D_B-E_B)$, which gives (CL.58).
A strict saving makes that exact deficit exceed $R$, proving (CL.59).
Duplicate cell incidences stay in $D_B$. A state live on one input
and certified on another stays in its live pool; it is not assigned
to $u$. No differently restricted graph or independently optimized
residual resource is combined with this one. $\square$

For the exact remaining obligation put

$$
Z_B^{\rm rem}=E_B-P_B-\mu_B\ge0.
$$

Then the original comparison $m\ge G$ is exactly equivalent to

$$
\sum_{B\in\mathcal L_*}
 \bigl(D_B-(\beta_B-1)-\Delta_B-\mu_B-Z_B^{\rm rem}\bigr)\le R.
\tag{CL.60}
$$

Indeed $P_B+\mu_B+Z_B^{\rm rem}=E_B$, so the left side is the
unchanged exact sum $\sum_{B\in\mathcal L_*}(D_B-E_B)$.
This equivalence is bookkeeping, not a separate compensation proof.
An empty $\mathcal L_*$ is already covered by the credited signs
of Section 7.

For a correct original full-fiber native preparer at both caps
$n+1,W+3$, use its particular conditional Boolean projection in
(CL.37). Here $r\ge0$ is the original additional-latch parameter
of Section 9. That projection obeys both Boolean caps and
$m\le H_P-4-r$, so (CL.58) gives

$$
H_P\ge G+4+r+R-\sum_{B\in\mathcal L_*}
 \bigl(D_B-(\beta_B-1)-\Delta_B-\mu_B\bigr).
\tag{CL.61}
$$

All right-hand data belong to that projection. This only applies the
displayed conditional full-fiber correspondence; it supplies no new
source or service bridge. The source remains the entire unbounded
fiber (CL.35), with its original homomorphism, complete current row,
eleven profiles, original positions and fixed pointwise code (CL.36).
Preparation still returns the literal original latch and enters the
complete original $e_0$ or $e_1$ on the same source. The four original
replies and separately installed edges (CL.39), two paid profile states
and all mandated latches keep their original meanings and charges.
The independently priced eight-state reader still returns the whole
predecessor row, including exterior, occurrences, canonical equality
partition, repetitions, disequalities and strict-prefix guards, with
at most two fresh calls and six letters. Every installed unused state
and every actual repeated or certified visit remains paid. Binding,
authentication, access, same-version data, export, isolation, code-only
handoff and stationary service remain the separate source and service
assumptions in Section 9. No acquisition, free history, clock, counter,
selector, address computation or physical resource conclusion follows.

## 16. Attribution and the remaining unrestricted alternative

SI supplies the actual-prefix and fixed-successor interfaces, the common
cuts, support envelopes, localization and exact incidence identities.
Its span-at-most-four and early-endpoint signs remain the credited
suppliers of $R\ge0$. Sections 3–6 supply the union capacity, eligible
private joins, combined membership and fixed-size cut capacity
$\kappa_v$, and the per-depth maximum $p_d$ in $P_B$. Those bounds
are retained without replacing their maximum by a sum. SI's
all-history both-conflict capacity, count relaxation, star and cyclic
injections, and complete above-grid inclusions retain their original
scope. The conditional native correspondence and original source,
profiles, entries and reader retain their separate supplied contracts.

The additional deductions are the descent of every alternative support
at a cell, the singleton-descent inequalities (CL.41), the resulting
host-saturation or two-child alternative, and the additional adjacent
depth charge (CL.48). Disjoint depth pairs turn that local propagation
into the nonnegative correction $\mu_B$ on top of $P_B$. Corollary
12.4 gives its nonzero consequence for two distinct simple edges when
the old demand bound has only its baseline, including bipartite demands.
The exact-baseline argument derives the host–support bijection before
using it for coordinate swaps and merging successors; it does not
infer singleton entire child families. Proposition 14.1 is only an
uncharged equality-case refinement. Finite union counting, integrality,
set cardinality identities and summation over disjoint sets are standard
tools. The residual rewrite (CL.60) is not additional mathematical
content. No external novelty or priority claim is made.

The correction can vanish. Ineligible joins generate no demand by this
route. A single-edge demand has $\nu_v=\kappa_v=2$ and does not
satisfy the new strict trigger. If both children already have
$\kappa\ge2$, their existing demand charges can absorb the forced
ambiguity, so (CL.48) supplies no extra unit under that configuration.
At a cell with one live child, ambiguity can descend along that arm
without forcing two ambiguous cells on its next depth. The final
internal layer has no internal adjacent pair. These are boundaries of
the deductions, not complete realizations or counterexamples. The
cone-equality arms can also reuse existing live states; no unspent
surplus from those arms has been proved.

What remains missing is a universal same-graph charge covering every
remaining duplicate incidence by actual unspent excess, genuine
never-live states and the collective reserve. No uniform positivity
of $\mu_B$, no inequality paying all $D_B$, and no separate
compensation theorem for every late pool is proved. Independent
residual lower bounds on overlapping coordinate sets cannot be
subtracted to manufacture that charge. All-input correctness, actual
termination and both full-run caps still constrain any prospective
construction, including its certified traffic and fixed successors.

For the unchanged all-size domain $\min(k,n-k+1)\ge4$, retain the
original alternatives: either prove collective compensation for every
complete original graph at both original $n,W$ caps, or provide a
complete correct strict-subgrid graph meeting both on every input.
Neither alternative is completed here. The supplied critical-instance
intervals are background; no improved numerical optimum or strict-subgrid
construction is asserted. The unrestricted-budget minimum remains a
separate question. These are ordinary symbolic deductions conditional
on the displayed interfaces, with no kernel, independent-review,
exhaustive-search, general-neural-network, empirical learning,
physical-resource or programme-completion claim.

## 追加锚（本行以下为增补区）
