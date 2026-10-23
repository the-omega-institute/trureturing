# Native threshold states and certificates for the costs of actual runs

## 1. Original domain and the two finite graph classes

**Definition 1.1 (positions, costs and Boolean tables).** Fix integers
$n\ge6$ and $3\le k\le n-2$, and positive integer positions
$A=\{s_1<\cdots<s_n\}$. Write

$$
c_i=s_i+4,\qquad W=\sum_{i=1}^n c_i,\qquad
C_R=\sum_{i\in R}c_i,\qquad G=k(n-k+1).
$$

A table $P$ consists of a finite installed set $Q$ of running states,
two distinct terminals $\mathsf0,\mathsf1$, one running start, a fixed
label $i(q)\in[n]$ at each $q\in Q$, and fixed successors
$\delta(q,0),\delta(q,1)\in Q\sqcup\{\mathsf0,\mathsf1\}$.
The entire mutable configuration is the current state. Every visit to
label $i$ costs one query and $c_i$, including every repeated visit and
every visit after the output has become logically determined. Put
$m=|Q|$, counting unreachable installed states and excluding the two
terminals. Let $m_i$ count installed states labelled $i$ and
$m(R)=\sum_{i\in R}m_i$.

Let $\mathcal T_{n,k}$ be the class of these tables whose actual run on
every $x\in\{0,1\}^n$ terminates with
$\mathbf1_{\{|x|\ge k\}}$ after at most $n$ queries. Let
$\mathcal F_{c,k}\subseteq\mathcal T_{n,k}$ impose, in addition,
weighted cost at most $W$ on every actual input. Define

$$
m_{\mathrm{exec}}(c,k)=\min_{P\in\mathcal F_{c,k}}|Q|.
$$

The supplied grid makes this minimum nonempty [PCA, Theorem 26.1][PCA];
see also [CP, Corollary 4.2][CP]. Neither class imposes an order, syntactic
read-once condition, leveling, acyclicity of the union graph, immediate
stopping at a certificate, or realizability of every syntactic path.
An inconsistent syntactic path need not be an actual input run.

**Definition 1.2 (actual live incidence).** A history is an actual
prefix ending immediately before a query. Let $S$ be its exposed
coordinate set and $\eta_S$ its assignment. Write
$h=|\eta_S^{-1}(1)|$ and $z=|\eta_S^{-1}(0)|$. The history is live
when both outputs have completions, equivalently when

$$
(h,z)\in V:=\{0,\ldots,k-1\}\times\{0,\ldots,n-k\}.
$$

Let $F_{h,z}$ be the installed hosts of actual live histories with
these counts, and $b_{h,z}=|F_{h,z}|$. Put

$$
Q_{\mathrm{live}}=\bigcup_{(h,z)\in V}F_{h,z},\qquad
u=|Q\setminus Q_{\mathrm{live}}|.
$$

A state visited both live and after certification belongs to
$Q_{\mathrm{live}}$ once. The number $u$ includes unreachable states
and states reached only after certification. Histories and their
assignments are mathematical indices, with no additional running
register supplied to $P$.

**Definition 1.3 (the original native correspondence).** Retain the
ordered free algebra and genuine substitution of [WTF, Definition
1.1][WTF]:

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
$$

At the cut $\{L,R\}^3$, let $R_*$ have the perfect ordered exterior,
equality classes

$$
\{LLL,LRL\}=a,\quad\{LLR\}=b_1,\quad\{LRR\}=b_2,
\quad\{RLL,RRL\}=c,\quad\{RLR\}=b_3,\quad\{RRR\}=b_4,
$$

and whole-subtree disequality between different classes. The domain is
the entire fiber

$$
\mathcal U_*=
\{u\in\mathcal T:R_{\{L,R\}^3}(\rho u)=R_*\}.
$$

There is no bound on source size, height or branch interiors. A complete
predecessor row retains its ordered exterior, occurrence holes,
canonical equality partition, disequalities and strict-prefix blocking
guards. Equal subtrees at different addresses retain their occurrences.
Pairing, order, addresses and observations are model structure in
addition to the two leaf atoms.

Use the exhaustive eleven profiles of WTF Definition 1.1. On $\Pi_j$,
$b_j$ is alpha, its left partner is beta and the other class roots are
branches. On $Z_d$ only class $d$ is beta; on $Z_*$ all roots are
branches. Define

$$
w_i=L^{s_i}R,\qquad a_i=LLLw_i,\qquad
\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}.
$$

Alpha, beta and absent each contribute zero. The required pointwise code
is the fixed function

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ is in any other zero profile}.
\end{cases}
$$

Preparation must reach the original literal latch
$\widehat e_{\sigma_{A,k}(u)}$ and hand off to the corresponding
original complete reader entry $e_{\sigma_{A,k}(u)}$, on the same
stationary register $\rho u$. The reader fixed in WTF Convention 1.3
has its separate eight installed states, at most two fresh calls and
six fresh letters, and returns the entire predecessor row.

A native preparer has one input-independent running start, one fixed
absolute address and four fixed successors per running state, the two
original-entry latches and $r\ge0$ further mandated distinct latches.
All installed states count, including unused states. Every actual
invocation is paid, including constant, root, absent, repeated and
post-certificate invocations. Its current state is the whole mutable
configuration. Keep the separate service hypotheses of WTF Assumption
1.5: actual update and register binding, acquired and authenticated
same-version row, lawful original-root permission, actual export,
complete access isolation, paid code-only handoff, lawful complete
entry, and stationary truthful service. Source acquisition, table and
address representation, entry contents, service storage, acquired-term
work, physical memory, elapsed time and energy retain separate prices.

Write $\mathsf N_{A,k,r}(H,p,\ell)$ and
$\mathsf B_{c,k}(m,t,J)$ for the exact feasibility predicates in WTF
Definitions 1.4 and 3.1. The reused transfer is precisely

$$
\mathsf N_{A,k,r}(H,p,\ell)
\ \Longleftrightarrow\
\mathsf B_{c,k}(H-4-r,p-1,\ell-3).
\tag{TC.1}
$$

Its proof is [WTF, Theorem 4.1][WTF], including its actual cube,
all-address classification, mandatory profile charge, projection and
full-fiber lift. Let $H_{\mathrm{exec}}(A,k;r)$ be the minimum native
preparation count at simultaneous caps $n+1,W+3$.

## 2. A sharp query cap separates the two live successors

**Lemma 2.1 (distinct live successors).** For every
$P\in\mathcal T_{n,k}$, a state reached by an actual live history
has two different successors. Weighted feasibility is not needed for
this lemma.

Proof. First consider any finite deterministic computation, with some
coordinates fixed externally, that computes threshold $a$ on $N$
free Boolean coordinates, where $1\le a\le N$, and terminates
correctly on every free assignment. It has an actual input requiring
at least $N$ free-coordinate queries. To prove this, answer successive
first exposures of free coordinates by one until $a-1$ ones have
been given, and by zero thereafter. Keep repeat answers consistent
and answer fixed coordinates by their fixed values. Before the $N$th
distinct free exposure, at most $a-1$ free ones and at most $N-a$
free zeros have been exposed. Both outputs still have completions.
Thus the computation cannot terminate correctly. It cannot revisit
a running state either: the replies on that repeated segment are fixed,
so every consistent completion would loop. Finitely many states and
total termination therefore force the $N$th distinct free exposure.
Completing the resulting partial assignment gives the required actual
input. Queries to fixed coordinates or repeats only add to its count.

Now take the stipulated live history of $P$. Let its exposed support
be $S$, let $d=|S|$, let $\ell$ be its number of queries, and let
$h$ be its ones. Put $R=[n]\setminus S$, $N=|R|$ and $a=k-h$.
Liveness gives $1\le a\le N$, and $\ell\ge d$.
Suppose its current state $q$ has
$\delta(q,0)=\delta(q,1)=r$. Freeze the assignment on $S$ in the
proof. Every assignment on $R$ follows the fixed old history and,
after the query at $q$, reaches $r$, independently of that query's
reply. Starting at $r$ therefore computes threshold $a$ on all $N$
free coordinates, using at most

$$
n-\ell-1\le n-d-1=N-1
$$

further queries on every assignment. This contradicts the preceding
query lower bound. The proof restriction supplies no running operation,
free bypass, external memory or new entry to the original table.
$\square$

## 3. Coherent representatives on seven coordinates

**Definition 3.1 (the chosen sixteen histories).** In this section
fix $n=7,k=4$ and $P\in\mathcal F_{c,4}$. For a live reply word
$w$, let $v(w)$ be the actual state after those replies and before
the next query. The supplied live freshness statement [SI, Theorem
2.2][SI] makes every word below an actual consistent history with
all its prefixes live. Use $f(h,z)=v(w_{h,z})$, with the words

| $h\backslash z$ | $0$ | $1$ | $2$ | $3$ |
| --- | --- | --- | --- | --- |
| $0$ | $\varepsilon$ | $0$ | $00$ | $000$ |
| $1$ | $1$ | $01$ | $100$ | $1000$ |
| $2$ | $11$ | $011$ | $0011$ | $00011$ |
| $3$ | $111$ | $0111$ | $00111$ | $000111$ |

The word specifies replies to actual fixed labels, rather than a fixed
coordinate order. Let $j$ be the label of the running start; all
nonempty displayed histories expose $j$ first.

**Lemma 3.2 (seven exclusions and two remaining collisions).** The
only possible equalities between different members of this
representative system are

$$
f(0,3)=f(3,0),\qquad f(1,3)=f(3,1).
\tag{TC.2}
$$

Proof. The following are reused facts about the full actual graph at
both caps, as collected and proved in SI Section 2 from PCA Theorems
34.3 and 35.1, PE Lemma 4.1, and WTF Theorem 9.1. Live queries are
fresh. Equal-hit histories with different supports cannot share a host;
equal-support histories with unequal hits cannot share; properly nested
supports cannot share. Different count cells sharing a host must, after
orienting their hits by $h<g$, satisfy

$$
g-h\ge2,\qquad z-w\ge2.
\tag{TC.3}
$$

These statements use the original distinct costs and both execution
caps. In particular they are stronger than abstract count-cell rules.

In the rectangle $\{0,1,2,3\}^2$, (TC.3) allows exactly nine
unordered pairs:

$$
\begin{aligned}
&(0,2)(2,0),\quad(0,2)(3,0),\quad(0,3)(2,0),\\
&(0,3)(3,0),\quad(0,3)(2,1),\quad(0,3)(3,1),\\
&(1,2)(3,0),\quad(1,3)(3,0),\quad(1,3)(3,1).
\end{aligned}
$$

Here juxtaposition denotes a pair of cells. Completeness follows by
listing $h=0,1$, then $g\ge h+2$, $z\ge2$ and $w\le z-2$.

For a hypothetical collision let $S$ be the smaller-hit history's
support and $T$ the larger-hit history's support. If they are equal or
nested the preceding exclusions already apply. For incomparable
supports use [PE, Theorem 3.1][PE]: if the old assignment on
$S\setminus T$ is all zero and that on $T\setminus S$ is all one,
then

$$
|S\setminus T|=|T\setminus S|,\qquad
C_{S\setminus T}=C_{T\setminus S}.
\tag{TC.4}
$$

No agreement on $S\cap T$ is required. We check both polarity
premises separately for all seven excluded pairs.

For $00$ versus $111$, and $000$ versus $11$, the lower history
is all zero and the higher history all one. For $000$ versus
$0111$, the higher history's only zero is at $j\in S\cap T$;
the lower history is all zero. For $1000$ versus $111$, the
lower history's only one is at $j\in S\cap T$; the higher
history is all one. Thus (TC.4) applies in each of these four
comparisons. It forces $|S|=|T|$, contradicting their respective
lengths $2,3$; $3,2$; $3,4$; and $4,3$.

For the other three exclusions the supports have equal size and share
all but at most one coordinate. The details are:

| Reply words | Guaranteed common coordinates | Private polarities |
| --- | --- | --- |
| $00,11$ | the first coordinate $j$ | lower all zero, higher all one |
| $000,011$ | the first two queried coordinates, since the first reply is $0$ in both | lower all zero; the higher history's only zero is $j$ |
| $100,111$ | the first two queried coordinates, since the first reply is $1$ in both | the lower history's only one is $j$; higher all one |

The common-prefix claims follow from the common start and the fixed
successors, and freshness makes the listed coordinates distinct. In
each incomparable case the two private sets are therefore disjoint
singletons. Both polarity premises hold, so (TC.4) would equate the
costs of two different individual coordinates, contrary to
$c_1<\cdots<c_7$. The equal-support cases were already excluded.
Exactly the two pairs in (TC.2) remain. Their four endpoints are
distinct cells; no state can realize both pairs, since that would
also identify an excluded cross pair. $\square$

**Lemma 3.3 (the central fork and its whole host pool).** If
$v(01)=v(10)$, neither collision in (TC.2) occurs. Thus either
collision forces $b_{1,1}\ge2$. Moreover $F_{1,1}$ is disjoint
from every other live cell's host set.

Proof. Suppose $v(01)=v(10)$. The equal-hit support exclusion in
SI Section 2 forces the supports of these two histories to agree.
Their second labels must therefore be the same coordinate $x\ne j$.
Consequently the supports of $000$ and $111$ both contain
$\{j,x\}$ and have size three. If their hosts coincided, equal
supports would be forbidden by their unequal hits. Otherwise their
private sets would be singletons. Their assignments are all zero
and all one respectively, so (TC.4) would equate distinct individual
costs. This excludes the first collision.

The common state $v(01)=v(10)$ has a fixed label $y$ fresh for
both histories, hence outside $\{j,x\}$. The supports of
$1000$ and $0111$ therefore both contain $\{j,x,y\}$ and
have size four. Equal supports again cannot share. Otherwise their
private sets are singletons. The low history's only one and the high
history's only zero occur at $j$ in their intersection. Their private
assignments are consequently all zero and all one. Equation (TC.4)
again contradicts distinct individual costs, excluding the second
collision.

The histories $01,10$ both host $(1,1)$, so contraposition gives
two distinct hosts when either collision occurs. Finally no other
cell in the $4\times4$ rectangle can satisfy (TC.3) with $(1,1)$
in either orientation. This proves disjointness from the entire
other-cell host union, rather than just the representatives.
$\square$

## 4. The exact seven-coordinate count and collective compensation

**Theorem 4.1 (coherent-fork compensation).** Every
$P\in\mathcal F_{c,4}$ on seven coordinates satisfies

$$
|Q_{\mathrm{live}}|\ge
16+\max(0,b_{1,1}-2),\qquad
m\ge16+u+\max(0,b_{1,1}-2).
\tag{TC.5}
$$

Proof. Let $\varepsilon_0$ and $\varepsilon_1$ indicate the two
equalities in (TC.2), respectively. By Lemma 3.2,

$$
|\operatorname{im}f|=16-\varepsilon_0-\varepsilon_1.
$$

Put $e=b_{1,1}-1\ge0$. Lemma 3.3 places all $e$ additional
central hosts outside $\operatorname{im}f$. If at least one
collision occurs, it also gives $e\ge1$.

It remains to find one further disjoint state when both collisions
occur. Write

$$
q=f(0,3)=f(3,0),\qquad q'=f(1,3)=f(3,1).
$$

The actual histories $0001$ and $1110$ show that
$\delta(q,1)\in F_{1,3}$ and
$\delta(q,0)\in F_{3,1}$. Both are live running successors.
Lemma 2.1 makes them different. At least one, call it $r$, is
different from $q'$.

This $r$ is outside the entire representative image. A host of
$(1,3)$ can equal a different-cell representative only at $(3,0)$
or $(3,1)$, by (TC.3). A host of $(3,1)$ can do so only at
$(0,3)$ or $(1,3)$. Equality to the $(1,3)$ or $(3,1)$
representative is equality to $q'$, already excluded. The remaining
representatives are both $q$. But $q$ already hosts $(0,3)$ and
$(3,0)$: adding $(1,3)$ violates (TC.3) with $(0,3)$, and
adding $(3,1)$ violates it with $(3,0)$. Thus $r\ne q$.
Lemma 3.3 also separates $r$ from every host of $(1,1)$.
This proves every disjointness needed for this additional count.

In all cases we have counted distinct actual live states giving

$$
|Q_{\mathrm{live}}|\ge
16-\varepsilon_0-\varepsilon_1+e+
\varepsilon_0\varepsilon_1.
$$

If both indicators vanish this is $16+e$. If either is positive,
the bound is $15+e$, with $e\ge1$. These imply the first
inequality in (TC.5), both for $b_{1,1}=1$ and for
$b_{1,1}\ge2$. Adding the actual complement of the live union
gives the second inequality. The extra state was a specified actual
fixed successor, not a separately charged separator. Certified traffic
may visit any of these states; it creates no second charge and was
never removed from the computation. $\square$

**Corollary 4.2 (the first middle instance).** For every positive
integer seven-element position set $A$,

$$
m_{\mathrm{exec}}(c,4)=16.
\tag{TC.6}
$$

Every minimizing graph has $u=0$ and $b_{1,1}\le2$.
In the full incidence accounting of [SI, Theorem 5.2][SI], every
such graph satisfies $D\le E$.

Proof. Theorem 4.1 gives the lower bound. The reused grid upper has
states $(h,z)\in\{0,1,2,3\}^2$, labels $h+z+1$, and the
fixed successors advancing the appropriate count until the fourth one
or fourth zero, then entering its output terminal. The invariant is
the actual numbers of exposed ones and zeros. It reads an initial
segment of coordinates $1,\ldots,7$, without repetition, computes
threshold four, and fits both caps on every input. There are sixteen
running states. The input $1110000$ uses all seven coordinates and
attains $7,W$ together. This is the supplied grid specialized to this
slice, not a restriction on competing tables. Equality and the two
minimizer conditions follow from (TC.5). Finally SI's exact identity
is $|Q_{\mathrm{live}}|=16+E-D$, so (TC.5) gives $D\le E$.
$\square$

**Corollary 4.3 (the surviving SI sum on this slice).** Use SI
Definitions 9.1 and 10.9 for the common-support intervals and their
actual incidence quantities. On seven coordinates with threshold four,
put

$$
\mathcal L_*=
\{B=(a,b):b-a\ge5,\ b>4\},\qquad
\mathcal A_*=\mathcal B\setminus\mathcal L_*.
$$

Then every qualifying graph satisfies the strengthened collective bound

$$
\sum_{B\in\mathcal L_*}(D_B-E_B)
\le E_{\mathrm{cut}}+
\sum_{B\in\mathcal A_*}(E_B-D_B)
-\max(0,b_{1,1}-2).
\tag{TC.7}
$$

Proof. The exact disjoint-pool accounting [SI, Theorem 9.3][SI] is

$$
|Q_{\mathrm{live}}|-16=
E_{\mathrm{cut}}+\sum_{B\in\mathcal B}(E_B-D_B).
$$

Substitute (TC.5) and rearrange. SI Section 10 already supplies
span-four compensation, separation for early-ending intervals of any
length, and nonnegativity of the terms indexed by $\mathcal A_*$.
Those results are reused here. No separate nonnegativity assertion for
each interval in $\mathcal L_*$ is needed or proved. $\square$

## 5. The unchanged native lift and residual-seven constraints

**Corollary 5.1 (exact original native count).** Under every source,
code, entry, access and simultaneous-budget hypothesis of Definition
1.3, for $|A|=7$, $k=4$ and every $r\ge0$,

$$
H_{\mathrm{exec}}(A,4;r)=20+r
\quad\text{at caps }8,\ W+3.
\tag{TC.8}
$$

Proof. Apply the exact existing equivalence (TC.1). A native
competitor with $H$ installed preparation states projects, without
copying states, to a correct Boolean table with at most $H-4-r$
running states and both caps $7,W$. Corollary 4.2 therefore gives
$H\ge20+r$.

Conversely lift the sixteen-state grid exactly as in WTF Theorem 4.1.
Install each coordinate-$i$ state at the shortest original literal
$a_i=LLL L^{s_i}R$. Branch uses its Boolean-one successor; alpha,
beta and absent each have their separately installed Boolean-zero
successor. Replace the two terminals by the original entry latches.
Add the two paid profile states, start at $D$, and retain all $r$
mandated latches:

| State | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | grid start | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

On every $Z_{b_3}$ source the original occurrence identity identifies
the selected run with the grid run on $\theta(x_a)$, for arbitrary
allowed branch interiors, alpha replies and absent selected addresses.
It pays at most $1+7$ calls and $3+W$ letters. The other ten
profiles follow the original profile analysis: alpha at $D$ is
$\Pi_3$; on its branch route only alpha at $T$ supplies the other
code-one profile $\Pi_4$. All other routes require zero. These routes
use at most two calls and six letters, within the same uniform caps.
The full fiber, original pointwise code and complete entries are thus
preserved. There are $16+2+2+r=20+r$ preparation states. The actual
cube origin for $1110000$, supplied by WTF Supplier 2.1, attains
$8,W+3$ together. Reader states and fresh reader costs remain
separate. This uses the existing transfer, without adding an encoder,
source copy, reset, reroot, equality port, workspace or acquisition
service. $\square$

**Corollary 5.2 (one installed vector, residual seven).** For any
$P\in\mathcal F_{c,k}$ in the full original parameter domain,
every actual live prefix with exposed support $S$, $h$ ones and

$$
R=[n]\setminus S,\qquad |R|=7,\qquad k-h=4
$$

satisfies $m(R)\ge16$. Such a prefix exists whenever
$\min(k,n-k+1)\ge4$.

For a native preparer at caps $n+1,W+3$, let $M_i$ count its
installed running states in the disjoint original selected-address
classes

$$
E_i=\{p w_i v:p\in\{LLL,LRL\},\
                    v\in\{\varepsilon,L,R\}\}.
$$

Every corresponding actual live cube prefix satisfies
$M(R):=\sum_{i\in R}M_i\ge16$. All these assertions concern
the same original vector $(m_i)$, or respectively $(M_i)$.

Proof. [CP, Theorem 5.1][CP] freezes the actual old assignment and
suppresses its fixed-coordinate chains. It gives a total residual
threshold-four graph on $R$, with one input-independent running start,
at most $m(R)$ installed running states and simultaneous caps $7,C_R$.
Realized edges follow the original subsequences; unrealized edges do
not become actual, and no state is copied. Reindexing the seven
remaining original positions preserves their positive increasing
integer costs. Apply Corollary 4.2 to obtain $m(R)\ge16$.

In the middle range the live pair

$$
h=k-4,\qquad z=n-k-3
$$

is nonnegative and has depth $n-7$. SI Theorem 2.2 realizes it
as an actual live history, proving existence of a qualifying prefix.
For the native assertion use the same actual selected-state projection
as in [CP, Corollary 5.2][CP]. It has $m_i\le M_i$ and both
Boolean caps, so the Boolean result implies $M(R)\ge16$.
All suppressed invocations remain paid in the original computation.

No inequalities for different prefixes are summed as disjoint resource
pools. In particular the statement concerns actual residual supports,
rather than all seven-element subsets independently. It removes the
inherited-cut condition from SI Theorem 10.8 for residual parameters
$N=7,q=4$ only. $\square$

**Corollary 5.3 (the next start-label constraint).** For $n=8$ and
$k=4$ or $k=5$, if $j$ is the start label, then

$$
\sum_{i\ne j}m_i\ge16.
$$

A hypothetical graph with $m=17$ must have exactly one installed
state labelled $j$.

Proof. At $k=4$ answer the first query zero; at $k=5$ answer it
one. Either is an actual live prefix leaving seven coordinates and
residual threshold four. Apply Corollary 5.2. The start itself gives
$m_j\ge1$, and subtracting the inequality from $m=17$ gives
$m_j\le1$. This does not assert existence or impossibility of such
a seventeen-state graph. $\square$

## 6. Exact costs of the complete actual runs

**Definition 6.1 (visit vectors and ordered gaps).** Fix now any
$P\in\mathcal T_{n,k}$, before assuming a weighted cap. For every
actual input $x$, let $v_i(x)$ count all visits to coordinate $i$,
and put

$$
t(x)=\sum_i v_i(x)\le n,\qquad e_i(x)=v_i(x)-1,\qquad
a_j(x)=\sum_{i=j+1}^n e_i(x)\quad(1\le j\le n-1).
$$

Thus certified repeats are included in $v$, with no truncation at the
first certificate. For strictly increasing costs write

$$
b=c_1,\qquad g_j=c_{j+1}-c_j,\qquad
p_1=0,\quad p_i=\sum_{j<i}g_j,\qquad c_i=b+p_i.
$$

Original costs have $b\ge5$ and $g_j\ge1$ integral. Write
$R=p_n$, $S_p=\sum_i p_i$, and
$L(P)=\{x:t(x)=n\}$. Let $B_P$ be the integer matrix with row
$a(x)$ for each $x\in L(P)$, retaining inputs as row indices even
when rows coincide. Matrix rows and chambers are proof coordinates,
with no running memory added to $P$.

**Theorem 6.2 (the exact common-offset ray).** For fixed positive
integer gaps $g$, the same table $P$ belongs to $\mathcal F_{c,k}$
exactly when

$$
B_Pg\le0,\qquad b\ge b_P(g),
\tag{TC.9}
$$

where

$$
b_P(g)=\max\left(
5,\ \max_{x:t(x)<n}
\left\lceil\frac{a(x)\cdot g}{n-t(x)}\right\rceil
\right).
\tag{TC.10}
$$

An empty inner maximum imposes no condition. If $B_Pg\not\le0$
the ray is empty; otherwise its admissible integer offsets are
precisely $b_P(g),b_P(g)+1,\ldots$. Moreover

$$
b_P(g)\le b_0(g):=
\max\{5,(n-1)R-S_p\}.
\tag{TC.11}
$$

Proof. Expand $c_i=b+\sum_{j<i}g_j$ and interchange finite sums:

$$
\begin{aligned}
J_c(x)-W
 &=\sum_i(v_i(x)-1)c_i\\
 &=(t(x)-n)b+\sum_{j=1}^{n-1}g_j a_j(x).
\end{aligned}
\tag{TC.12}
$$

For $t(x)=n$ this is the corresponding row of $B_Pg$,
independent of $b$. For $t(x)<n$ it is nonpositive exactly at
the ceiling in (TC.10). The intersection of all actual input
constraints proves (TC.9) and the exact ray.

For a shorter run of length $t$, put $r_x=a(x)\cdot g$.
Since $0\le p_i\le R$,

$$
r_x=\sum_i v_i(x)p_i-S_p\le tR-S_p.
$$

Set $A_0=(n-1)R-S_p$. Because $p_1=0$ and the other
$n-1$ offsets are at most $R$, we have $A_0\ge0$. For
$t\le n-1$,

$$
(n-t)A_0-(tR-S_p)
  =(n-1-t)(nR-S_p)\ge0.
$$

It follows that $r_x/(n-t)\le A_0$. The number $A_0$ is an
integer, so its ceiling has the same bound. Taking the maximum with
five proves (TC.11). This argument retains the multiplicity of every
visit on every complete run. $\square$

**Corollary 6.3 (monotonicity and eventual stabilization).** Fix gaps
$g$ and the associated offsets $p_i$. The function

$$
b\longmapsto m_{\mathrm{exec}}((b+p_i)_{i=1}^n,k),
\qquad b\in\mathbb Z,\ b\ge5,
$$

is nonincreasing, and is constant for every $b\ge b_0(g)$.
Its stable value is

$$
\min\{|Q_P|:P\in\mathcal T_{n,k},\ B_Pg\le0\}.
\tag{TC.13}
$$

For any original $c$, integer $h\ge0$ and positive integer $q$,

$$
m_{\mathrm{exec}}(c+h\mathbf1,k)
 \le m_{\mathrm{exec}}(c,k),\qquad
m_{\mathrm{exec}}(qc,k)=m_{\mathrm{exec}}(c,k).
$$

Proof. Increasing $b$ by $h$ changes each actual excess by
$h(t(x)-n)\le0$, so preserves feasibility. Theorem 6.2 makes
every shorter-run constraint automatic for every table once
$b\ge b_0(g)$; beyond that bound the feasible set of tables
is precisely the set in (TC.13). The grid belongs to that set, so
its installed counts have a minimum. Scaling $c$ by $q>0$
multiplies every actual excess by $q$, giving exactly the same
feasible tables. All these cost vectors are admissible original
position instances, with positions obtained by subtracting four.
They compare different parameter instances; they do not authorize
changing the supplied code or addresses within a fixed native task.
No independence from the gaps is asserted. $\square$

## 7. Equality faces and a sparse full-length obstruction

**Theorem 7.1 (finite sign cells, including their faces).** For fixed
$n,k$, the exact minimum is constant on every sign cell of the finite
arrangement

$$
(v-\mathbf1)\cdot c=0,
\qquad v\in\mathbb Z_{\ge0}^n,\quad\sum_i v_i\le n,
\quad v\ne\mathbf1,
\tag{TC.14}
$$

intersected with the admissible original integer costs. There are at
most $\binom{2n}{n}-1$ listed nonzero forms. A sign cell records
each sign as negative, zero or positive, so equality faces are included.

Proof. The actual run and visit vector of any fixed
$P\in\mathcal T_{n,k}$ do not depend on its costs. Its weighted
feasibility tests precisely whether the form for each of its actual
visit vectors is nonpositive. Identical sign patterns in (TC.14)
therefore give identical feasible tables, and hence identical minima.
There are $\binom{2n}{n}$ nonnegative integer vectors with total
at most $n$, by adding a slack coordinate and counting compositions
of $n$ into $n+1$ parts. Only $v=\mathbf1$ gives the zero
normal, and deleting it gives the stated upper bound. Repeated or
proportional forms may reduce the number of hyperplanes further.
$\square$

**Proposition 7.2 (an actual equality face and the correctness
premise).** Let $P_{43}$ be the Boolean selected graph specified by
the thirteen-state table and four disjoint fallback grids in [PCA,
Proposition 36.1][PCA]. It is a correct seven-query threshold-four
table with forty-three running states. For every original increasing
cost vector on its seven labels,

$$
P_{43}\in\mathcal F_{c,4}
\quad\Longleftrightarrow\quad c_2+c_5=c_3+c_4
\quad\Longleftrightarrow\quad g_2=g_4.
\tag{TC.15}
$$

In contrast, a positive full-length cost cone need not imply
threshold correctness when the premise $P\in\mathcal T_{n,k}$
is omitted.

Proof. Use the complete fixed graph at the cited location, including
all thirty fallback states, rather than just its local merger. Its
all-input correctness and seven-query bound follow from the supplied
head, scan and exit analysis. Write $X=\{2,5\}$,
$Y=\{3,4\}$ and $U=\{6,7\}$. Its shared heads are
$\lambda:(x_1,x_2,x_5)=(0,0,0)$ and
$\mu:(x_1,x_3,x_4)=(1,1,1)$.
After scanning $U$, a shared route exits through OR on $X$, a
single query to coordinate one, or AND on $Y$.

The all-zero input follows coordinates $(1,2,5,6,7,2,5)$ and
has excess $C_X-C_Y$. The all-one input follows
$(1,3,4,6,7,3,4)$ and has excess $C_Y-C_X$. Both have
length seven, proving necessity of equality and its invariance under
any common offset. Conversely, if $C_X=C_Y$, a shared head and
scan cost $c_1+C_X+C_U$. A two-query exit costs at most
$C_X=C_Y$, while the single-query exit costs $c_1<C_X$.
Thus every shared route costs at most $W$; fallback routes query
distinct coordinates and also cost at most $W$. This proves
sufficiency. The equation $C_X-C_Y=g_4-g_2$ gives the gap
form. Full-length fallback routes read every coordinate once. The
two-query shared exits either do likewise or repeat exactly $X$
while omitting $Y$, or repeat exactly $Y$ while omitting $X$.
Consequently their full-length suffix rows are exactly

$$
0,\qquad (0,-1,0,1,0,0),\qquad(0,1,0,-1,0,0).
$$

The zero row is attained, for example, on $0100111$, whose fallback
route reads all seven distinct coordinates. The all-zero and all-one
inputs above attain the other two rows.

This is a correct above-grid sharing graph; its size is $43>16$.
Its cost dependence does not prove cost dependence of the optimal
minimum.

For the final assertion use the complete ten-state graph in [SI,
Theorem 7.2][SI]. Every run queries a prefix of its six coordinates
without repetition, so it satisfies both cost caps for all positive
costs and all its length-six suffix rows are zero. Its positive gap
cone is therefore the whole positive orthant. Yet on $000011$ it
returns one after coordinates $(1,2,3,4,5)$, while threshold three
is zero. This explicit source-specified graph proves that passing the
cost conditions cannot replace correctness. $\square$

**Theorem 7.3 (exclusive sparse actual-run alternative).** For every
fixed $P\in\mathcal T_{n,k}$, exactly one of the following holds.

1. The same Boolean table, with every installed state retained, is in
   $\mathcal F_{c,k}$ for some original positive integer position set.
   Equivalently there exists $g\in\mathbb Z_{>0}^{n-1}$ with
   $B_Pg\le0$.
2. There are $1\le s\le n-1$ actual inputs
   $x_1,\ldots,x_s\in L(P)$ and positive rational coefficients
   $\lambda_1,\ldots,\lambda_s$ such that

$$
z=\sum_{\ell=1}^s\lambda_\ell a(x_\ell)\ge0,
\qquad z\ne0.
\tag{TC.16}
$$

In the second alternative the coefficients may be chosen as positive
integers, or normalized to sum one. The selected runs exclude this
table for every strictly increasing original cost vector, regardless
of its common offset. The first alternative is also equivalent to
nonemptiness of the real cone

$$
\mathcal C(P)=\{g\in\mathbb R^{n-1}:g_j>0,\ B_Pg\le0\}.
\tag{TC.17}
$$

Proof. Actual original feasibility supplies the positive integer gaps
by (TC.12) on the full-length runs. Conversely, given these gaps,
choose $b\ge b_0(g)$ integral in Theorem 6.2. This makes every
actual run feasible, with $s_i=b+p_i-4$ positive and strictly
increasing. Correctness, query counts, transitions and installed states
have not changed.

For exhaustiveness use the existing finite rational inequality-Farkas
theorem [Dvorak--Kolmogorov, Theorem 1.2][DK]. Its repository supplier
is `D5.S3.Analytic.Convexity.FarkasAlternative.inequality_farkas`,
with the owning [FarkasAlternative Scribe][FS]. Its exact finite
mapping is: row type $I=L(P)$, column type $J=[n-1]$,
field $\mathbb Q$, matrix $B_P$, right-hand side
$b_F=-B_P\mathbf1$. All types are finite and equality on $I$
is decidable. The supplier says exactly one of

$$
\exists y\ge0:\ B_Py\le-B_P\mathbf1
$$

and

$$
\exists\lambda\ge0:\quad
z=B_P^{\mathsf T}\lambda\ge0,\qquad
(-B_P\mathbf1)\cdot\lambda<0
$$

holds over $\mathbb Q$. The first branch is the rational condition
$g=\mathbf1+y\ge\mathbf1$, $B_Pg\le0$; clearing
denominators gives positive integer gaps. The last strict inequality
in the second branch is $-\sum_j z_j<0$. Together with $z\ge0$
it says precisely $z\ne0$. This is an application of the supplied
general alternative with its stated signs and nonnegativity domains.

To prove the sparse bound, retain a rational representation of this
fixed nonzero $z$ by rows with positive coefficients. If it uses
more than $d=n-1$ rows, they are rationally linearly dependent.
Choose a nonzero rational dependence $\sum_\ell\alpha_\ell
a(x_\ell)=0$ and reverse its sign if necessary so that some
$\alpha_\ell>0$. Subtract

$$
\tau\alpha_\ell\quad\text{from each }\lambda_\ell,
\qquad
\tau=\min_{\alpha_\ell>0}
\frac{\lambda_\ell}{\alpha_\ell}.
$$

All resulting coefficients are nonnegative, at least one vanishes,
and their represented vector is still $z$. Delete zeros and iterate.
This terminates with at most $d$ positive rational coefficients.
Clear their denominators for integer coefficients, or divide by their
positive sum for a rational probability distribution.

For any positive real gaps $g$, (TC.16) gives $z\cdot g>0$.
But $B_Pg\le0$ would give
$z\cdot g=\sum_\ell\lambda_\ell a(x_\ell)\cdot g\le0$.
Thus the alternatives are incompatible, and a real point of
$\mathcal C(P)$ excludes the rational dual. The rational Farkas
alternative then supplies rational, and hence integer, positive gaps.
This proves the real-cone equivalence without discarding equality
faces or assuming an interior rational approximation.

Finally, on full-length runs (TC.12) gives

$$
\sum_\ell\lambda_\ell(J_c(x_\ell)-W)
   =z\cdot g>0.
$$

At least one selected actual input violates its own cap. All runs
belong to the one complete table; no independently optimized runs or
residual pools have been combined. $\square$

## 8. A bounded original position witness

**Theorem 8.1 (integer witness with $c_n\le n^n$).** Fix
$n\ge6$, $3\le k\le n-2$ and $P\in\mathcal T_{n,k}$.
If this same Boolean table is weighted-feasible at any original
position set, then it is weighted-feasible at another original position
set $A'$ with

$$
5\le c'_1<\cdots<c'_n\le n^n,
\qquad 1\le s'_1<\cdots<s'_n\le n^n-4.
\tag{TC.18}
$$

Every installed state, fixed label, successor, actual input trajectory
and query count is preserved. This is an existence statement across
admissible cost instances, rather than a modification of a specified
original instance.

Proof. Form the real polyhedron

$$
\mathcal P=\left\{c\in\mathbb R^n:
\begin{array}{l}
e(x)\cdot c\le0\quad\text{for every }x\in\{0,1\}^n,\\
-c_1\le-5,\\
c_i-c_{i+1}\le-1\quad(1\le i<n)
\end{array}\right\}.
$$

The hypothesis makes it nonempty. Its constraints imply $c_i\ge i+4$.
For any feasible point $c^0$, the sublevel
$\{c\in\mathcal P:\sum_i c_i\le\sum_i c_i^0\}$ is
closed and bounded, since each coordinate has a fixed lower bound and
the coordinate sum has an upper bound. It is compact, so the sum
has a minimum. Its minimizing face is nonempty and compact. Successive
minimization of coordinates on this face produces a unique point
$c^*$. If $c^*$ were a nontrivial midpoint of two feasible points,
their sums would both be minimal, then their first coordinates would
both be minimal on that face, and so on through all coordinates.
They would coincide with $c^*$. Thus $c^*$ is an extreme point
of $\mathcal P$.

The active constraint normals at $c^*$ span $\mathbb R^n$.
Otherwise a nonzero vector orthogonal to all of them would permit
sufficiently small perturbations in both signs: active equalities
would persist and all finitely many strict inequalities would remain
strict. This would express $c^*$ as a nontrivial midpoint.
Choose $n$ independent active rows. Write their integer system as
$Hc^*=b_H$, so $\det H\ne0$. Budget rows have right-hand
side zero, the floor row has right-hand side $-5$, and gap rows
have right-hand side $-1$.

We bound the determinant of each matrix $H_i$ obtained by replacing
column $i$ of $H$ by $b_H$. A budget row has normal $e=v-\mathbf1$,
where $v\ge0$ is integral and $t=\sum_jv_j\le n$. Hence

$$
\|e\|_2^2=\sum_jv_j^2-2t+n
 \le t^2-2t+n\le n(n-1).
$$

The last bound follows by maximizing the convex quadratic on
$[0,n]$ at its endpoints: their values are $n$ and $n(n-1)$.
Replacing one entry by its zero right-hand side cannot increase this
norm. A gap row has norm at most $\sqrt3$ after replacement:
its original two nonzero entries have magnitude one and the new
right-hand-side entry has magnitude one. The floor row has norm
at most $\sqrt{26}$ after replacement, since its original entry
has magnitude one and its right-hand side has magnitude five.
For $n\ge6$ every row of every $H_i$ consequently has norm
at most $n$.

Hadamard's inequality now gives $|\det H_i|\le n^n$. Indeed,
successive orthogonalization of independent rows preserves the
absolute determinant and makes it the product of their orthogonal
lengths, each at most the original row norm; dependent rows have
determinant zero. Set $D=|\det H|\in\mathbb Z_{\ge1}$ and
$c'=Dc^*$. Cramer's rule gives

$$
c'_i=\operatorname{sgn}(\det H)\det H_i\in\mathbb Z,
\qquad 0<c'_i\le n^n.
$$

Moreover $c'_1\ge5D\ge5$ and
$c'_{i+1}-c'_i\ge D\ge1$. All budget inequalities are
homogeneous, so they remain true under this scaling. The original
positions $s'_i=c'_i-4$ therefore have exactly the properties in
(TC.18), and every actual input of $P$ meets its new weighted cap.
Neither graph surgery nor an assumption on full-run realizability was
used. All installed unreachable states are still installed.
$\square$

**Corollary 8.2 (finite position reduction for a strict saving).** For
fixed admissible $n,k$, a correct graph with $m<G$ exists at both
caps for some original $A$ if and only if one exists with
$s_n\le n^n-4$. At $n=7$ the witness bounds are
$c_7\le823543$ and $s_7\le823539$; Corollary 4.2 independently
excludes a strict saving in that slice.

Proof. Apply Theorem 8.1 to any purported strict-subgrid graph; its
installed count does not change. The converse is immediate since the
bounded positions are admissible original positions. The numerical
values are $7^7$ and $7^7-4$. The bound is a finite reduction,
not a bound on a practical running time for finding or excluding such
a graph. $\square$

## 9. The remaining universal implication and original programme

**Theorem 9.1 (an equivalent all-position target).** Fix admissible
$n,k$. The following assertions are equivalent.

1. For every original positive integer position set $A$,
   $m_{\mathrm{exec}}(c,k)=G$.
2. Every $P\in\mathcal T_{n,k}$ with $|Q|<G$ has the
   sparse full-length actual-run obstruction (TC.16).
3. No $P\in\mathcal T_{n,k}$ with $|Q|<G$ has a
   nonempty positive gap cone (TC.17).
4. There is no correct strict-subgrid graph at both original caps with
   $s_n\le n^n-4$.

Proof. Theorem 7.3 identifies failure of the obstruction with existence
of admissible feasible costs for that same table, proving the
equivalence of the first three assertions using the supplied grid
upper $G$. Corollary 8.2 gives the fourth. These implications retain
all installed states and complete actual runs. In particular the
quantifier over correct $n$-query tables in assertion 2 has not been
discharged by the general Farkas theorem. $\square$

**Corollary 9.2 (native meaning of the alternative).** Under the
unchanged hypotheses of Definition 1.3, the all-position equality in
Theorem 9.1 is equivalent to

$$
H_{\mathrm{exec}}(A,k;r)=G+4+r
\quad\text{for every original }A\text{ and every }r\ge0.
$$

If a particular correct subgrid Boolean table has no obstruction,
Theorems 7.3 and 8.1 provide some bounded original $A'$ and its
full-fiber native lift at count $m+4+r$ and caps $n+1,W'+3$.
They provide no feasibility assertion at a different specified $A$.

Proof. Use (TC.1) separately at each parameter set. The projection
preserves actual selected subsequences and both cap inequalities;
the lift installs literal addresses for that parameter set, all four
successors, the two paid profile states, the original two latches and
$r$ extra latches. At fixed $A'$ its stationary source, prescribed
$\sigma_{A',k}$ and complete reader entries are unchanged. Changing
from $A$ to $A'$ changes the mathematical parameter instance and
the installed native literals; it is not a runtime source operation or
a permitted code reselection inside the fixed-$A$ task. $\square$

**Definition 9.3 (outstanding requirements and applicability).** The
unrestricted all-$n,k$ middle-range equality, a general proof of the
state-shortage-to-obstruction implication in Theorem 9.1, and the
equivalent surviving global SI inequality for late intervals of span
at least five remain open here. The seven-coordinate collision list
does not cover larger rectangles: for example $(0,4),(2,2)$ is
an additional count-eligible pair at $n=8,k=4$. No complete correct
strict-subgrid graph is supplied. The current total bounds at
$n=8,k=4$ remain $17\le m_{\mathrm{exec}}\le20$; Corollary
5.3 is an additional constraint on one installed vector.

The exact seven-coordinate result, its residual-seven consumer, and
the complete-run cost deductions above are repository deductions with
their ordinary proofs. The grid, local support and polarity exclusions,
prefix restriction, SI span-four and early-ending results, and exact
native transfer are reused at their cited scopes. Finite rational
duality is the literature-attested supplier [DK]; Cramer's rule,
Hadamard's inequality and finite conic elimination are established
linear algebra used inside the cost application. No priority claim
follows from these attributions or from absence of a textual match.

The classical symmetric-function normalization in [Wegener, Chapter
14, Section 4, printed pages 423--425][Wegener] is for BP1; its
proof on page 424 explicitly relies on realizability of every graph
path. [Bryant, Section 2, Definition 1][Bryant] imposes strictly
increasing variable indices. [Cook--Edmonds--Medabalimi--Pitassi,
Section 2.1][CEMP] uses acyclic graphs and read-once consistent
accepting paths. [Li--McKenzie, Section 2.7][LM] likewise defines
its deterministic programs as DAGs and its read-$k$ condition
syntactically. Those hypotheses do not follow from freshness only
while live. None of those results is used to normalize the arbitrary
shared tables of Definition 1.1.

The wider alpha/beta programme still requires the same-source internal
observer and conditions for recovering the four expressions of space,
time, boundary and memory. Finite installed cardinalities alone do not
settle those recoveries. Acquired data versus callable source access,
arbitrary busy cuts, coherent infinite-source constructions, late-target
requirements and acquisition/authentication/export services retain their
original obligations. The ordered tree and observation interfaces are
declared model structure; neither their mathematical existence nor a
finite native table asserts physical realization or total physical
runtime. The finite theorem (TC.8) discharges one parameter slice of
the installed-state frontier, rather than these larger requirements.

[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[CP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_COMMON_PREFIX_MEMORY_FRONTIER.md
[SI]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SUPPORT_INCIDENCE_AND_COUNT_RELAXATION.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[WTF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHTED_THRESHOLD_FRONTIER.md
[DK]: https://arxiv.org/html/2409.08119v3
[FS]: ../../../Blueprint/D5/S3/Analytic/Convexity/FarkasAlternative.scribe.cs
[Wegener]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[Bryant]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[CEMP]: https://doi.org/10.4230/LIPIcs.ICALP.2016.36
[LM]: https://arxiv.org/html/2305.11276

## 追加锚（本行以下为增补区）
