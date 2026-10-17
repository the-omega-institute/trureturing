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
