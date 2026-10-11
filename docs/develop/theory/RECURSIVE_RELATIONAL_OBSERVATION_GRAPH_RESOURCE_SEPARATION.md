# Acquired graph relations, exact strategy resources and whole-fiber separation

This volume gives ordinary mathematical proofs for the entire graph family
of [ARH, Definition 27.1][ARH], with every finite mixed literal history and
every finite prefix-free original target cut. Its source size and physical
query words are unbounded. The additional bridge is an exact interpretation
of common physical actions on the two coupled copies, followed by exact
whole-row terminal predicates. It discharges the resource decision
obligation left after ARH's all-depth existence decision. The synchronous
resource theorem is not presumed to apply outside its named family.

The manuscript is pure theory, not a kernel proof or an implemented solver.
Its definitions and ordinary proofs are reference material. Existing source
volumes remain the suppliers of their stated results. Subsequent additions
belong after the append anchor; no accepted source statement is revised here.

## 1. The acquired input and the actual comparison class

**Definition 1.1 (trees, replies and complete rows).** Write

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{GRS.1}
$$

All trees are finite, nonempty, free and ordered. Physical words are in
$\Sigma^*$, where $\Sigma=\{L,R\}$; the root is $\varepsilon$.
The reply $r_t(p)$ is in
$\mathcal A=\{\alpha,\beta,\mathsf b,\bot\}$, with $\mathsf b$ meaning
branch and $\bot$ meaning absent. The subtree $t|_p$ exists only when
$p\in\operatorname{Pos}(t)$.

For a finite prefix-free original cut $Q$, the complete row $R_Q(t)$ has
the reached members of $Q$ in lexicographic order, the entire concrete
outside with those subtrees replaced by numbered holes, and the partition
of hole occurrences by equality of their complete ordered subtrees. Thus
an absent cut makes no hole; the root cut gives one hole; the empty cut
keeps the entire concrete tree. Repeated equal subtrees are distinct
occurrences in the row and belong to the same partition class.

**Assumption 1.2 (exactly the graph input).** The old cut, concrete outside,
old partition and acquired relation are

$$
\begin{gathered}
P=\{L,R\},\qquad C=\langle\square_1,\square_2\rangle,
\qquad\pi=\{\{1\},\{2\}\},\\
e_*=(0,L,1,R,=).
\end{gathered}
\tag{GRS.2}
$$

The equality record requires BOTH endpoints to exist and compares their
whole trees. There is an arbitrary finite list $H_0$ of literal records
$(a,p,c)$, including repetitions and absent replies. Its epochs are
nonnegative integers. The target $Q$ is any finite prefix-free set of
original words. No synchronous, constructor-elimination, orbit or target
recognizer is an additional premise. The entire logical fiber is

$$
U=\{u:R_P(u)=(C,\pi),\quad
        \operatorname{Rel}_{e_*}(u),\quad
        r_{\rho^a u}(p)=c\text{ for every }(a,p,c)\in H_0\}.
\tag{GRS.3}
$$

This is the family of ARH27.1, not a claim about arbitrary extra signed
relations. In particular its old disequality between the two children is
retained. The sign in (GRS.2) does not stand for equality of root replies.

Records come from legal paid acquisition, and a complete accessible-state
cut leaves exactly a recoverable encoding of these records and the common
parameters. The same actual register, at its original root, has reached a
certified

$$
N\ge\max\bigl(\{1\}\cup\operatorname{epochs}(H_0)\bigr).
\tag{GRS.4}
$$

The complete-state and paid-acquisition meanings are [ARH, Assumption 1.3
and Proposition 2.1][ARH]. In particular an accessible description, address,
length, counter, program position, timing field, permission, archive or
other source-dependent residue must be included in the state. No forgotten
traversal survives this cut. Source continuity is not a source identity
label. Service statements concern $U\ne\varnothing$; logical empty inputs
are explicitly treated separately.

**Definition 1.3 (services and resources).** A comparator is any deterministic
effective program which correctly outputs the entire $R_Q(u)$ and halts
on every $u\in U$. Its source operations are actual original-root
$\mathsf{Read}(p)$ for any finite word, forward $\mathsf{ApplyRho}$ on the
same register, and absorbing $\mathsf{Halt}$. Address, update and halt
choices may depend on acquired replies. Local computation uses only the
common initial state and the actual replies. There is no reset, clone,
reroot, unknown equality, source-membership, chart, hidden code or identity
port. Updates reveal no source-dependent side channel. A new entry after
halt is a separately supplied operation.

For a run set

$$
\begin{aligned}
c_A(u)&=(q_A(u),d_A(u),\ell_A(u)),&
\ell_A(u)&=\sum_{\text{actual new reads at }p}|p|,\\
b(A)&=(\sup_U q_A,\sup_U d_A,\sup_U\ell_A),&
\mathcal F&=\{b\in\mathbb N^3:\exists A\ b(A)\le b\},\\
W_\lambda(A)&=\sup_{u\in U}
 (\lambda_q q_A(u)+\lambda_d d_A(u)+\lambda_\ell\ell_A(u)),&
W_\lambda^*&=\inf_A W_\lambda(A),\quad
\lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{GRS.5}
$$

Every call, including a repeat or an absent reply, costs one read; a root
word has length zero. Each run is finite, so zero weights are applied to
finite integers before the supremum. There is no expression
$0\cdot\infty$ inside a run. Coordinate maxima can occur on different
sources. Acquisition, local work, storage, address generation, installation,
output, certification, physical time and energy are separately supplied
and charged. None is optimized or refunded by (GRS.5). No fixed running
time, source-size bound or halt time is assumed.

## 2. A single full source behind two physical copies

**Proposition 2.1 (the supplied graph and its exact action interface).** Put

$$
F(y)=\langle\rho(y),y\rangle,\qquad
V=\{y\in\mathcal T:
 r_{\rho^aF(y)}(p)=c\text{ for all }(a,p,c)\in H_0\}.
\tag{GRS.6}
$$

The supplier [ARH, Theorem 8.2 and (27.2)][ARH] gives the bijection
$F:V\to U$. For every $y\in V$, every integer $j\ge0$ and every suffix
$z\in\Sigma^*$, the following are identities of the actual replies:

$$
\begin{aligned}
r_{\rho^j F(y)}(\varepsilon)&=\mathsf b,\\
r_{\rho^j F(y)}(Lz)&=r_{\rho^{j+1}y}(z),\\
r_{\rho^j F(y)}(Rz)&=r_{\rho^j y}(z).
\end{aligned}
\tag{GRS.7}
$$

Every physical read address is uniquely one of these three forms. Its physical
length is respectively zero or $1+|z|$. The suffix and the choice $L/R$
are common action data chosen before the unknown source is quantified.

Proof. To make explicit what is retained in the supplied bijection, the
old row says $u=\langle a,b\rangle$ with $a\ne b$. Both relation endpoints
are reached, and its equation says $a=\rho(b)$. Conversely every
$\langle\rho(y),y\rangle$ has this old row and both endpoints. The supplied
clock $\kappa(\alpha)=0$, $\kappa(\beta)=1$,
$\kappa(\langle a,b\rangle)=2+\kappa(b)$ satisfies
$\kappa(\rho y)=\kappa(y)+1$, so the old disequality holds for every finite
$y$. The literal conjunction gives exactly $V$ in both directions.
The inverse parameter is mathematically $u|_R$; this is not an acquired
operation. This spells out the supplier's whole-source correspondence,
including its old inequality and guards.

Distribution of $\rho$ over the original root gives
$\rho^jF(y)=\langle\rho^{j+1}y,\rho^j y\rangle$. Navigating the first
letter proves (GRS.7), also when the remaining word is empty, is absent,
or reaches a descendant born inside a leaf image. Every nonempty word has
one first letter and one suffix. The physical request remains $Lz$ or
$Rz$ at the original root; no source root is moved. Actual application
of $\rho$ raises both displayed exponents by one. Thus the same $y$
controls every reply through an entire run, on both sides. $\square$

**Lemma 2.2 (full finite-tree formulas for the graph action).** There are
effective formulas in ordinary two-valued WS2S for the exact domain $V$
and every reply in (GRS.7), at fixed epoch numerals and with arbitrary
suffix-position variables. Source quantifiers range over complete finite
trees with unrestricted continuations below every queried position.

Proof. Use the infinite binary successor tree as the position universe.
Encode a tree by three finite sets $Y_\alpha,Y_\beta,Y_{\mathsf b}$.
Their union $T_Y$ must satisfy these finite-set formulas:

- The sets are pairwise disjoint and $\varepsilon\in T_Y$.
- Every nonroot member is a child of a member of $Y_{\mathsf b}$.
- Every member of $Y_{\mathsf b}$ has both children in $T_Y$.
- A member of $Y_\alpha\cup Y_\beta$ has neither child in $T_Y$.

Call this conjunction $\mathsf{Tree}(Y)$. Following the unique parents
of a position reaches the root; hence disconnected components are
excluded. The child requirements give exactly a nonempty finite ordered
full binary tree. Conversely its three actual label sets satisfy the
formula. This is a bijective coding, without padding or extra nodes.

For each fixed $k\ge0$, compute the two finite trees $\rho^k\alpha$ and
$\rho^k\beta$. For $c\in\{\alpha,\beta,\mathsf b\}$ define

$$
\begin{aligned}
\mathsf{Rep}_{k,c}(Y,z)\ \Longleftrightarrow\quad&
 [c=\mathsf b\ \land\ z\in Y_{\mathsf b}]\\
 &\lor\!\bigvee_{\substack{a\in\{\alpha,\beta\},\ w\in\operatorname{Pos}(\rho^k a)\\
                          r_{\rho^k a}(w)=c}}
   \exists v\ (v\in Y_a\land z=vw).
\end{aligned}
\tag{GRS.8}
$$

Every $w$ in this finite disjunction is a fixed literal word. Thus $vw$
means a fixed composition of successor symbols, not concatenation of
two variable words. Let $\mathsf{Rep}_{k,\bot}$ be the complement of the
three nonabsent formulas. Original branch nodes are preserved by $\rho$;
every other node of $\rho^k y$ lies in the finite image of a unique
original leaf. These parts are disjoint. It follows that, on
$\mathsf{Tree}(Y)$, precisely one reply formula is true and it equals
$r_{\rho^k y}(z)$. This proves both directions, including absent and born
positions, arbitrary tree shapes, $k=0$ and $z=\varepsilon$.

For a physical address annotation write

$$
\begin{aligned}
\mathsf G_{j,c}(Y;\varepsilon)&=[c=\mathsf b],\\
\mathsf G_{j,c}(Y;L,z)&=\mathsf{Rep}_{j+1,c}(Y,z),\\
\mathsf G_{j,c}(Y;R,z)&=\mathsf{Rep}_{j,c}(Y,z).
\end{aligned}
\tag{GRS.9}
$$

For any fixed word $p$, the notation $\mathsf G_{j,c}(Y;p)$ uses its
unique root/first-letter factorization. The exact domain formula is

$$
\mathsf{Adm}(Y)=\mathsf{Tree}(Y)\land
  \bigwedge_{(a,p,c)\in H_0}\mathsf G_{a,c}(Y;p).
\tag{GRS.10}
$$

By Proposition 2.1 its satisfying assignments are exactly the entire
original $U$, bijectively. Each retained literal, including a repeated
or inconsistent one, participates. The old row and guarded acquired
equality are satisfied by both inclusions of that proposition; they
have not been relaxed in (GRS.10). There are not separate independently
quantified left and right sources.

The formula uses no source truncation at the markers. For example, when
$z$ is an original branch, the whole of both descendant subtrees is
still in $T_Y$, subject to the same literal conjunction. It can have
arbitrary finite size. The position variables can also lie outside
$T_Y$, where the leaf-image disjunction or its complement decides the
reply. Marker support is not a bound on source support.

The WS2S interfaces just used are finite-set membership, Boolean
operations, quantification over positions and finite sets, and fixed
successor compositions. They are precisely those in [MONA, §§7.1–7.2,
printed pp. 39–40][MONA]. Its decidability theorem therefore applies to
these formulas and their quantified Boolean combinations. Formula
(GRS.8) reuses the fixed-epoch reply construction of [SRF, Lemma 1.4][SRF].
The additional interpretation is (GRS.9)–(GRS.10) on one shared whole
graph parameter, with the two different exponents forced by actual
physical copies. No general closure for shifted subtree equality is
being assumed. $\square$

## 3. Terminal labels for the entire original row

**Definition 3.1 (the supplied all-depth gate).** Apply [ARH, Theorem 30.2
and Corollary 31.1][ARH] to precisely Assumption 1.2. Call its nonempty
positive outcome $\mathsf{Fin}$. It decides, with both stopping directions,
whether an original depth $H$ determines $R_Q$ on all of $U$. On
$\mathsf{Fin}$ it supplies such an inclusive depth $H$ and a correct
static service with sufficient budgets

$$
K_0=2(2^{H+1}-1),\qquad
L_0=K_0(H+\lceil N/2\rceil),\qquad (K_0,0,L_0).
\tag{GRS.11}
$$

A known constant row, including the root cut, can instead use
$K_0=L_0=0$. These numbers are sufficient, not asserted optimal.
On a nonempty negative outcome, the supplier constructs finite bad pairs
in the same fiber at every requested original depth and excludes every
uniformly read-bounded serial service. The logical empty flag is separate.

**Proposition 3.2 (effective exact full-row fibers on the positive gate).**
On $\mathsf{Fin}$ one can compute the exact finite set
$\mathscr R=R_Q(U)$ and WS2S formulas $\mathsf{Row}_r(Y)$ for
$r\in\mathscr R$ such that

$$
\mathsf{Adm}(Y)\Longrightarrow
 [\mathsf{Row}_r(Y)\ \Longleftrightarrow\ R_Q(F(y))=r].
\tag{GRS.12}
$$

Every $r$ is attained by an actual finite source. Equal rows get one label,
even if obtained from different original prefix patterns.

Proof. List all functions $\theta:\{p:|p|\le H\}\to\mathcal A$ and form

$$
\mathsf C_\theta(Y)=\mathsf{Adm}(Y)\land
   \bigwedge_{|p|\le H}\mathsf G_{0,\theta(p)}(Y;p).
\tag{GRS.13}
$$

This is an effective finite list of exact full-source formulas. Decide
the emptiness of each by Lemma 2.2. For a nonempty cell enumerate finite
$y$ until one satisfies it. This succeeds because the cell has a finite
tree witness, and concrete membership is decidable. Alternatively use
a finite model from the decision. Compute $F(y)$ and its whole $R_Q$.

Every admitted tree is in exactly one cell, since its original replies
are unique. Any two trees in that cell agree through original depth $H$;
the supplied determining-prefix theorem makes their whole rows equal.
Consequently the computed row is correct on the entire cell, including
all its arbitrarily large continuations. Compare the computed reached
lists, concrete numbered contexts and complete partitions and merge
equal rows. Set $\mathsf{Row}_r$ to the disjunction of exactly the cells
labelled by $r$. This proves (GRS.12), exhaustion and attainment.

No sample is substituted for a universal source domain: the witness
computes the finite output of a cell whose constancy has already been
proved. The terminal predicate still quantifies all of that cell.
This is the prefix-to-label method of [SRF, Proposition 1.5][SRF] with
its hypotheses supplied by the graph gate and (GRS.10), not an application
of SRF's synchronous membership assumption. $\square$

This order matters. A general WS2S formula for equality of two arbitrary
shifted graph subtrees is not needed or asserted. The ARH graph decision
first handles nested and incomparable target comparisons on the whole
domain. Only its positive finite-prefix conclusion licenses (GRS.13).
On its negative branch, finite labels are not manufactured by choosing
one source per purported output.

## 4. Deciding bounded actions with genuinely unbounded words

**Definition 4.1 (finite adaptive skeleton and exact path).** For given
$q,d\in\mathbb N$, a skeleton is a finite rooted tree with at most $q$
read nodes on a root-to-leaf path. Each read has four reply children,
an epoch numeral $j_v\in\{N,\ldots,N+d\}$, and one of the address forms
$\varepsilon$, $(L,z_v)$ or $(R,z_v)$. Epochs are nondecreasing along
paths. Each leaf is an absorbing halt with a label in $\mathscr R$.
The same $z_v$ is used by every source reaching that read node.

For a leaf $t$, let $\mathsf{Path}_t(Y;\mathbf z)$ be the conjunction of
its edge-reply formulas (GRS.9). Define

$$
\begin{aligned}
E_t(\mathbf z)&=\exists Y\,
  [\mathsf{Adm}(Y)\land\mathsf{Path}_t(Y;\mathbf z)],\\
k_t&=\#\{v:v\prec t\},\qquad
d_t=\begin{cases}j_{\rm last}-N,&k_t>0,\\0,&k_t=0,\end{cases}\\
L_t(\mathbf z)&=\sum_{\substack{v\prec t\\\text{form }L\text{ or }R}}
                    (1+|z_v|).
\end{aligned}
\tag{GRS.14}
$$

Here $Y$ denotes the three finite label sets; all read ancestors are
counted in $k_t$, including root reads. The formula for $L_t$ is a
mathematical cost expression, not a claim that arbitrary variable-length
arithmetic is definable in WS2S. Unreachable leaves have no actual cost.

**Theorem 4.2 (whole-family bounded-budget decision).** For every logical
graph input and every $q,d\in\mathbb N$, it is decidable whether a service
in Definition 1.3 has $\sup_U q_A\le q$ and $\sup_U d_A\le d$.
Both answers terminate. A positive answer yields an effective actual
service. Physical words range over all finite words; no length cutoff
or uniform halt-time premise is imposed.

Proof. Decide empty-domain status and the gate of Definition 3.1. On an
empty fiber return the vacuous immediate halt. On a nonempty negative
gate return no, by its universal serial exclusion. On a positive gate
construct $\mathscr R$ and its predicates by Proposition 3.2.

There are finitely many skeleton shapes of read depth at most $q$, epoch
annotations, root/left/right annotations and leaf labels. For each decide

$$
\exists(z_v)_v\ \forall Y\quad
 \left[\mathsf{Adm}(Y)\Longrightarrow
   \bigwedge_t\bigl(
    \mathsf{Path}_t(Y;\mathbf z)\Longrightarrow
    \mathsf{Row}_{r_t}(Y)\bigr)\right].
\tag{GRS.15}
$$

Only nonroot address forms have a suffix variable. All such variables
are outside the source quantifier. The logical formulas of Lemma 2.2
and Proposition 3.2 make this a WS2S sentence; hence it has a terminating
decision independent of any depth bound on its words. The universal
finite sets encode every entire finite source in $U$. Existentially
choosing a different address for each $Y$ would be a different, invalid
formula for this operational problem.

If the sentence is true, extract its finite suffix tuple. One effective
method is to enumerate tuples of finite words and decide the remaining
fixed-tuple sentence until a successful tuple is found. This enumeration
is performed only after the existence decision returned true. Install
the resulting finite table. Before each reached read perform the actual
nonnegative epoch difference and submit its full physical word. At a
leaf output its stored entire row and halt. Proposition 2.1 and Lemma
2.2 inductively identify each actual reply with the formula for that
same $Y$. Thus its reached leaf satisfies (GRS.15) and outputs its whole
original row. Its actual cost is (GRS.14), within the requested budgets.
There is no chart selection, free current-source description or hidden
comparison during execution.

Conversely take ANY permitted comparator meeting the two uniform bounds.
At a reachable reply prefix, common initial state and the acquired
replies determine its ensuing local work, updates and next physical read
or halt. The segment is finite: at least one admitted source reaches it
and the comparator is total on that source. There are at most
$1+4+\cdots+4^q$ reachable reply prefixes. Unroll these fixed segments.
Keep every early halt, and replace every unreachable child by immediate
halt. Delete updates after the final read on any terminating branch;
they reveal no information and the same output can be computed earlier.
This decreases update cost and leaves reads and lengths unchanged.

The result is a finite skeleton with its actual finite words and
nondecreasing epoch numerals. Each word has exactly the factorization
in Proposition 2.1. Every reached output is in $\mathscr R$ by correctness;
an unreachable halt may receive any member of this nonempty set. The
skeleton therefore belongs to the finite enumeration and satisfies
(GRS.15). This is an existence argument covering arbitrary source-total
code, not an algorithm extracting its reachable control graph. It
requires no a priori bound on the code's local work, address lengths,
source size or time to halt. Both operational directions are proved.
$\square$

**Corollary 4.3 (finite length bounds and exact source witnesses).** Every
finite upper triple $(q,d,L)$ is decidable. An accepted triple has a
finite actual service. For any constructed skeleton with fixed words,
exact reachable leaves, coordinate maxima and same-run weighted maxima
are computable; every nonempty leaf has a finite original-source witness.

Proof. In addition to the finite choices in Theorem 4.2, enumerate the
finitely many physical words of length at most $L$. Test (GRS.15), then
decide $E_t$ for each leaf and require $L_t\le L$ only where $E_t$ is
true. All remaining tests are either WS2S sentences with fixed words or
integer comparisons. A comparator within the triple bound has every
reached address of length at most $L$; unreachable parts can be deleted
as in the necessity proof. Thus this finite enumeration is complete.

For a nonempty leaf extract a finite $y$ satisfying its exact path and
domain, then form the original $F(y)$. The reply correspondence puts
this source on that actual leaf. Every admitted source reaches one leaf,
and the leaf costs are precisely $(k_t,d_t,L_t)$. Taking each coordinate
maximum gives $b(A)$; taking the weighted sum at each leaf BEFORE its
maximum gives $W_\lambda(A)$. Distinct coordinate maxima need not have
the same witness. $\square$

At $q=0$, (GRS.15) asks for one whole-row label valid throughout the
entire fiber. A zero-read controller cannot use updates to learn a label.
Early halts are not padded with reads, so neither zero-budget statements
nor later price statements charge unreachable or post-halt actions.
The finite-control argument is the established [JRF, §4][JRF] and
[SRF, §2][SRF] method. The source, action and whole-row obligations that
permit its use on the entire graph are Propositions 2.1 and 3.2 and
Lemma 2.2, rather than a change in those suppliers' scopes.

## 5. Attained complete coordinate frontier and separate same-run prices

**Lemma 5.1 (same-source normalization on the graph).** Put
$D_N=\max(N,5)-N$. Every comparator $A$ has an effective replacement $A'$ with
the same output on each same source, no greater value in any of its
three sourcewise costs, and

$$
d_{A'}(u)\le D_N,\qquad q_{A'}(u)\le\ell_{A'}(u)\quad(u\in U).
\tag{GRS.16}
$$

Proof. [ABC, Proposition 6.4][ABC], using [JRF, Theorem 3.1][JRF], caps
actual epochs at $\max(N,5)$ on every source in an acquired signed fiber.
Its hypotheses are the common complete control, actual serial actions,
and source-totality in Assumption 1.2 and Definition 1.3. The reply and
nonexpansive length identities are valid on all finite original trees,
so they restrict to exactly $U$, including its old inequality and acquired
graph. They give the same output, preserve read count, decrease length,
and replace each source's update count by its minimum with $D_N$.
Simulated late updates are local computations, not actual receipts.

In this graph the physical root is always a branch by (GRS.7). Simulate
every root reply by that known constant without a raw call. This removes
only source-independent calls, preserves the simulated controller and
its finite termination, and does not increase any charged coordinate.
Every remaining actual read has length at least one, proving (GRS.16).
This specializes the supplied cleanup with no residual zero-length
information allowance. $\square$

**Theorem 5.2 (effective complete Pareto basis).** On a nonempty positive
gate, a terminating algorithm computes a finite nonempty set
$\mathcal B\subseteq\mathbb N^3$ such that

$$
\mathcal B=\operatorname{Min}(\mathcal F),\qquad
\mathcal F=\{b\in\mathbb N^3:\exists v\in\mathcal B\ v\le b\}.
\tag{GRS.17}
$$

For each $v$ it constructs a legal service with exact worst vector $v$
and finite source witnesses for its coordinate maxima. On a nonempty
negative gate, $\mathcal F$ is empty and every correct service has both
unbounded worst read count and unbounded worst submitted-length sum.

Proof. This uses the cofinal-grid and Pareto method of [JRF, Lemma 5.2
and Theorem 5.3][JRF]. Its exact hypotheses here are the whole-domain
positive/negative gate of Definition 3.1, the static supplier (GRS.11),
the same-source cap and cleanup in Lemma 5.1, the unbounded-address
decision of Theorem 4.2, and the triple decision of Corollary 4.3.
The supplier's literal-only source feasibility routine is not used.

Set $K=\max(K_0,L_0)$. First decide every pair
$0\le q\le K$, $0\le d\le D_N$ by Theorem 4.2, leaving physical words
unbounded. For each true pair extract a finite service and its finite
worst length $L^{\rm wit}_{q,d}$. Only then use Corollary 4.3 to find
the least feasible $L_{q,d}$ in the finite interval
$0\le L\le L^{\rm wit}_{q,d}$. Retain the minimal elements among the
resulting triples. This terminates: there are finitely many pairs,
false pairs never start an address enumeration, and each true pair
provides its own finite upper endpoint for length minimization.

For completeness take any finite-budget comparator and normalize it by
Lemma 5.1. Let $q',L'$ be its worst reads and length, so $q'\le L'$.
If $q'\le K$, its read/update pair lies in the grid and the least length
for that pair is at most $L'$. If $q'>K$, then $q'>K_0$ and $L'>L_0$;
the static supplier is no worse in all three coordinate maxima. The grid
is therefore cofinal in the entire original comparison class. This step
compares worst coordinates, not the cost on each same source.

Every retained triple is feasible. Cofinality proves equality of the
upward closures and hence (GRS.17). At a minimal retained triple the
actual worst vector of its witness cannot be strictly smaller: it too
would be feasible, contradicting minimality. Corollary 4.3 provides the
actual-source maxima. This proves attainment as well as the upper-budget
description; it does not claim that arbitrary larger exact cost vectors
can be independently installed.

On a negative gate no uniform finite read service exists, by the gate.
If some correct service had finite worst length, deleting its constant
root reads would give a uniform read bound by the proof of (GRS.16), a
contradiction. This proves both unboundedness statements. $\square$

**Corollary 5.3 (extended budgets and sourcewise traversal).** Let
$\overline{\mathbb N}=\mathbb N\cup\{\infty\}$ and allow upper budgets
in this set. On a positive gate their feasible region is the upward
closure of the same finite $\mathcal B$ in
$\overline{\mathbb N}^{3}$. On a nonempty negative gate it is exactly

$$
\{(\infty,d,\infty):d\in\overline{\mathbb N}\},
\tag{GRS.18}
$$

with its minimal extended vector $(\infty,0,\infty)$ attained by a
source-total static service. On a logical empty fiber the convention of
nonnegative empty suprema equal to zero gives basis $\{(0,0,0)\}$.
This last case is not an actual acquired entry.

Proof. At the fixed actual epoch $N$, the paid original-node decoder
of [SLH, Theorem 2.2][SLH] recovers an original reply with at most two
current physical reads. Decode the root and recurse on the original
children only after a decoded branch. The original tree is finite,
so this reconstructs it and its entire $R_Q$ with finitely many reads
on each source and zero updates. It creates neither inverse execution
nor free original observations. On a negative gate its two uniform
costs are infinite by Theorem 5.2. This proves (GRS.18).

On a positive gate a comparator with finite read bound has a finite
reachable reply tree by the necessity proof of Theorem 4.2. Sourcewise
termination makes each of its finitely many segments finite, so its
actual update and length maxima are finite as well. A finite length
bound reduces to this case after deleting root reads. In either case
Theorem 5.2 supplies a basis vector no greater than the resulting
extended budget. If both read and length bounds are infinite, the static
supplier fits any nonnegative update bound. Conversely a basis witness
meets every larger extended budget. Empty-domain correctness is vacuous
and is witnessed by immediate output of any fixed row. $\square$

**Theorem 5.4 (attained nonnegative rational same-run optimum).** For all
$\lambda\in\mathbb Q_{\ge0}^3$, the exact value $W_\lambda^*$ is
effectively computable in $\mathbb Q_{\ge0}\cup\{\infty\}$ and is
attained by a source-total actual service. More precisely:

- If $\lambda_q=\lambda_\ell=0$, its value is zero on every input.
- If $U\ne\varnothing$, the gate is negative and
  $\lambda_q+\lambda_\ell>0$, its value is infinity.
- On a nonempty positive gate it is a finite rational attained by a
  finite service and by a source witnessing that service's worst sum.
- On the logical empty fiber its value is zero under the same convention
  as Corollary 5.3.

Proof. The static sourcewise traversal proves the first case, even when
the unpriced read and length maxima are infinite. The negative case
follows from the separate unboundedness in Theorem 5.2 and nonnegativity
of the weights. The traversal attains this extended supremum; no single
finite-source run has infinite cost.

For a positive gate use the separate same-run method of [JRF, Theorem
7.1][JRF], after the following hypothesis match and threshold proof.
The static supplier has value at most
$B_0=\lambda_q K_0+\lambda_\ell L_0$. Lemma 5.1 decreases each cost on
each SAME source and so does not increase its weighted sum. Every
comparator of value at most $B_0$, including ones with unbounded unpriced
coordinates, can therefore be compared within update bound $D_N$.

Suppose at least one of the read and length weights is positive. If
$\lambda_q>0$ take $k_\lambda=\lfloor B_0/\lambda_q\rfloor$. If
$\lambda_q=0<\lambda_\ell$, use (GRS.16) to take
$k_\lambda=\lfloor B_0/\lambda_\ell\rfloor$. This bounds the read
depth after normalization in both cases. For a threshold $b\in[0,B_0]$
we can decide the existence of a correct skeleton satisfying, at each
reachable leaf,

$$
\lambda_q k_t+\lambda_d d_t+\lambda_\ell L_t\le b.
\tag{GRS.19}
$$

If $\lambda_\ell>0$, every reached physical word has length at most
$\lfloor B_0/\lambda_\ell\rfloor$. Enumerate those words and the finite
skeleton choices under $k_\lambda,D_N$. Test correctness, exact reachability
and (GRS.19) by Corollary 4.3. If $\lambda_\ell=0$, then
$\lambda_q>0$ and the displayed leaf cost is independent of suffixes.
For every numerically over-budget leaf conjoin $\neg E_t(\mathbf z)$
inside the existential suffix scope of (GRS.15). This is a WS2S
unbounded-address decision by Lemma 2.2. It introduces no arithmetic
comparison between variable lengths. Neither procedure charges an
unreachable leaf.

Every original comparator under the threshold normalizes sourcewise
and unrolls to one of these skeletons without increasing its weighted
sum. Conversely a successful skeleton actually executes (GRS.19) on
each source. These are both threshold directions against the entire
comparison class. Take a common positive denominator $a$ of the weights.
Each finite run sum lies in $a^{-1}\mathbb N$. A bounded nonempty set
of these sums has a maximum in that lattice. Test the finitely many
thresholds $0,1/a,\ldots,B_0$; the static supplier ensures a true test.
The first true one is the exact infimum and gives an attaining service.
Corollary 4.3 gives a source attaining its worst sum.

This proof does not minimize $\lambda\cdot b(A)$ or infer a same-run
optimum from the Pareto basis. The cofinal substitution in Theorem 5.2
is not asserted to dominate on each source and is not used here.
$\square$

**Corollary 5.5 (degenerate targets and finite source domains).** The
preceding decisions include zero reads, ground sources, the root cut,
the empty cut and absent target positions, with the following consequences.
On a nonempty fiber the root cut has exact basis $\{(0,0,0)\}$ and all
prices zero. The empty cut has a finite-budget service if and only if
$U$ is finite. A singleton fiber has a zero-cost service for every $Q$;
several ground possibilities are not assumed to be distinguishable for
free. An absent target address contributes no hole or equality class.

Proof. The root-cut row is constant. For the empty cut the output is the
entire original source. A uniform read bound gives finitely many terminal
outputs by the finite reply-tree argument, so $U$ must be finite.
Conversely, for finite $U$, take the maximum height of its sources.
Agreement of all replies through that height forces equality of the
entire source, because its leaves terminate all deeper paths. This is a
determining prefix, so the gate is positive and its paid static supplier
applies. These are existence statements with a decision supplied by the
same graph gate; no enumeration of a possibly infinite fiber is presumed.

For a singleton fiber every full row is constant; nonemptiness allows
its finite witness to be found, and its row can be installed as a root
halt. Installation remains separately charged. Ground and nonground
trees alike have exactly the label-set codes of Lemma 2.2; no discarded
chart or zero-coordinate exception arises. Finally Proposition 3.2
computes the actual reached cut list from an entire source in each
proved constant cell, so it includes absent positions with precisely
the semantics of Definition 1.1. $\square$

## 6. A scalable consumer on an infinite complete fiber

**Definition 6.1 (public perfect template).** For $m\ge1$ let
$B_0=\alpha$, $B_{i+1}=\langle B_i,B_i\rangle$, and put $g=B_m$.
Here $B_0$ is a tree, unrelated to the scalar upper price in Theorem 5.4.
Keep the entire graph input (GRS.2), and choose

$$
H_0^{(m)}=\{(0,RRw,\alpha):w\in\Sigma^m\},\qquad
Q=\{L,RL,RR\},\qquad N\ge1.
\tag{GRS.20}
$$

The template is a common finite consequence of the actual retained
literals. Its preparation and storage are not new free source evidence.

**Proposition 6.2 (both inclusions and both entire rows).** The entire
fiber of (GRS.20) is

$$
U_m=\{u_z=
 \langle\langle\rho(z),\rho(g)\rangle,\langle z,g\rangle\rangle:
 z\in\mathcal T\}.
\tag{GRS.21}
$$

There is no size, shape or equality restriction on $z$. All three target
cuts are reached, their concrete outside is
$\langle\square_1,\langle\square_2,\square_3\rangle\rangle$, and their
entire values are

$$
\rho(\langle z,g\rangle),\quad z,\quad g.
\tag{GRS.22}
$$

The first hole is always a singleton class. The two possible full rows
are consequently indexed by $z=g$: the partitions are respectively
$\{\{1\},\{2,3\}\}$ and $\{\{1\},\{2\},\{3\}\}$.

Proof. Write an arbitrary admitted source as $F(y)$ by Proposition 2.1.
Every word $Rw$ of length $m+1$ in $y$ has the required reply $\alpha$.
Reach of these words forces $y$ to be a branch and its right subtree
to have every level-$m$ position as an $\alpha$ leaf. All their proper
prefixes must be branches, and no leaf has a descendant. Thus that
subtree is exactly $g$, and $y=\langle z,g\rangle$ with arbitrary left
subtree $z$. Conversely every such $y$ satisfies every displayed literal,
so (GRS.21) has both inclusions. The graph record's guards exist, and
the old children remain unequal by the clock, for every such $z$.
ARH Proposition 2.1's paid producer can acquire this old row, these
literals and the relation before the stipulated complete cut; no
uniform pre-cut traversal bound is claimed.

Navigation gives (GRS.22) and the complete displayed exterior. If
$|t|$ counts all tree nodes, then $|\rho t|\ge|t|$, by induction using
the two leaf images. Hence

$$
|\rho(\langle z,g\rangle)|
 =1+|\rho z|+|\rho g|>|z|,\ |g|.
\tag{GRS.23}
$$

The first value cannot equal either other value. The remaining equality
is precisely $z=g$, and both cases occur. These comparisons account for
the whole partition, not just an extracted Boolean task. $\square$

**Theorem 6.3 (sharp resources against both copies and adaptive updates).**
For (GRS.20), put

$$
M=2^m,\qquad D=m+2+\lfloor N/2\rfloor.
\tag{GRS.24}
$$

Its exact Pareto basis and every nonnegative rational same-run optimum are

$$
\boxed{\ \mathcal B_m=\{(M,0,MD)\},\qquad
 W_\lambda^*=M\lambda_q+MD\lambda_\ell.\ }
\tag{GRS.25}
$$

Every permitted correct comparator, regardless of how it adapts its
updates and reads, satisfies the simultaneous accepting-run bounds

$$
q_A(u_g)\ge M,\qquad \ell_A(u_g)\ge MD.
\tag{GRS.26}
$$

Proof of the upper bound. Let $k=\lfloor N/2\rfloor$. At static epoch
$N$ submit, in any fixed order, the $M$ physical words

$$
RLwR^k\quad(w\in\Sigma^m).
\tag{GRS.27}
$$

Compare every reply with $c_N(\alpha)$, equal to $\alpha$ for even $N$
and $\beta$ for odd $N$. [SLH, Lemma 55.2 and Theorem 55.3][SLH]
say that these are the delayed leaf certificate for the known template
$g$ in the entire all-shape comparison domain $z\in\mathcal T$.
The extra prefix $RL$ is the actual original occurrence of $z$ and has
length two. Thus all replies match if and only if $z=g$, even when a
comparison tree has a different shape or stops before a template leaf.
Output the corresponding entire row from Proposition 6.2 and halt;
one may stop on the first mismatch. Every path has at most $M$ reads
and total length at most $MD$, with no updates. On $u_g$ all $M$ words
are read. This proves simultaneous attainment from above.

Proof of the universal same-run lower bound. For each $w\in\Sigma^m$
let $g^{(w)}$ change only the leaf at $w$ of $g$ from $\alpha$ to $\beta$.
Every $u_{g^{(w)}}$ is in the SAME full fiber (GRS.21), with a different
entire row from $u_g$. There is no restriction to this finite test family
in the theorem; these are admissible competitors used for its lower bound.

At any actual epoch $j\ge N$, a difference between $u_g$ and
$u_{g^{(w)}}$ is confined to the union of the two physical cones

$$
\mathcal D_w=RLw\Sigma^*\ \cup\ LLw\Sigma^*.
\tag{GRS.28}
$$

Strict ancestors of these occurrences remain branches, and all other
original components agree. In the first cone the two variable leaf
images are $\rho^j\alpha,\rho^j\beta$; in the second they are
$\rho^{j+1}\alpha,\rho^{j+1}\beta$. These are coupled changes of the
same $z$ in both copies, not independent modifications.

For any integer $n\ge0$, the two trees $\rho^n\alpha$ and
$\rho^n\beta$ agree at every word of length less than $\lfloor n/2\rfloor$.
This is part of the sharp leaf-separation supplier SLH55.2. It can also
be checked from $T_i=\rho^i\alpha$, $T_0=\alpha,T_1=\beta$ and
$T_i=\langle T_{i-1},T_{i-2}\rangle$ for $i\ge2$: a word of length
$r<\lfloor n/2\rfloor$ has weight at most $2r\le n-2$; every prefix
stays at an index at least two and both final replies are branches.
Therefore every physical read separating this pair at epoch $j$ has
length at least

$$
m+2+\lfloor j/2\rfloor\ \ge\ D;
\tag{GRS.29}
$$

the second cone has the possibly larger bound with $j+1$.

Now follow the actual accepting run of an arbitrary correct comparator
on $u_g$. For every $w$, this run must contain a read that separates
$u_g$ from $u_{g^{(w)}}$. Otherwise induction on its finite events gives
the identical acquired replies, control, actual updates and halt on
that alternative, producing the wrong full row. At the first separating
read for that alternative both runs have the same epoch, so (GRS.29)
applies even under adaptive updates. Different $w$ have disjoint unions
$\mathcal D_w$: within each copy their length-$m$ words are incomparable,
and the two copies start with different first letters. One read on the
accepting run can therefore separate at most one of these alternatives.
At least $M$ distinct actual read occurrences, each of length at least
$D$, must occur on that ONE run. This proves (GRS.26).

Nonnegative update counts and (GRS.26) put every worst vector above
$(M,0,MD)$ and every same-run weighted supremum above the value in
(GRS.25), including all zero weights. The static service attains both
bounds. This proves the claimed full frontier and weighted optimum
without restricting physical words, source size, local work or updates.
$\square$

The SLH certificate itself is supplied mathematics. The additional
lower-bound step is the simultaneous packing of all $M$ alternative
changes into disjoint unions of two physical cones on one accepting run,
uniformly over every later actual epoch. Applying a one-copy static
certificate theorem alone would not justify (GRS.26).

## 7. Two distinct failures of discarding source relations

**Proposition 7.1 (one representative per row changes the price).** Fix
one $w_0\in\Sigma^m$ and replace the source domain of the consumer by
the two-source set $\{u_g,u_{g^{(w_0)}}\}$, while retaining the same
entry epoch, action interface and full-row outputs. This is one
representative for each actual row. Its Pareto basis is
$\{(1,0,D)\}$, and its same-run price is
$\lambda_q+D\lambda_\ell$. For $m\ge1$ it therefore fails to preserve
the whole-fiber resource problem, whose two positive coordinates are
larger by the factor $2^m$.

Proof. The one word $RLw_0R^{\lfloor N/2\rfloor}$ distinguishes the
two leaf images and hence the two whole rows. It has length $D$ and
needs no update. Zero reads cannot select their different rows. The
first differing read of any correct adaptive comparator must have
length at least $D$ by the same two-copy, all-epoch calculation
(GRS.28)–(GRS.29). Both runs reach that read, giving the simultaneous
lower bound and the weighted statement. The full-fiber values are
Theorem 6.3. $\square$

This comparison preserves the set of row VALUES but discards sources
inside a row fiber. It is an invalid experimental shortcut for the
original task, not a competing acquisition theorem on $U_m$. The
prefix-cell witnesses in Proposition 3.2 are different: they merely
compute labels, while every formula (GRS.15) still quantifies every
admitted source, not those witnesses alone.

**Theorem 7.2 (deleting only the acquired graph equality).** Delete only
the equality in (GRS.2), retaining its two endpoint-existence guards,
the full old row, every literal in (GRS.20), the original target and
the same certified entry. The resulting entire fiber is

$$
U_m^-=\{\langle a,\langle z,g\rangle\rangle:
             a,z\in\mathcal T,\ a\ne\langle z,g\rangle\}.
\tag{GRS.30}
$$

For every $h\ge0$ it has two finite sources agreeing at ALL original
words of length at most $h$ but having different entire $Q$ rows.
No permitted serial service on $U_m^-$ has a uniform finite read bound
or a uniform finite submitted-length bound. Nevertheless a static
service terminates on each source and returns its row.

Proof. The retained old row requires a root pair with distinct children.
The same complete-leaf argument as Proposition 6.2 forces its right
child to be $\langle z,g\rangle$. Without the graph equation its left
child $a$ is unrestricted apart from the old disequality. This gives
both inclusions in (GRS.30). The endpoint $L$ at epoch zero exists;
the endpoint $R$ at epoch one is $\rho(\langle z,g\rangle)$ and exists.
Thus retaining the two guards imposes no lost condition. The deleted
predicate alone is the equation $a=\rho(\langle z,g\rangle)$.

Choose $k>\max(h,m)$, let $z=B_k$, and let $z'$ change one depth-$k$
leaf of $z$ to $\beta$. Take

$$
v=\langle z,\langle z,g\rangle\rangle,\qquad
v'=\langle z',\langle z,g\rangle\rangle.
\tag{GRS.31}
$$

Their old distinctness holds because $|z'|=|z|<|\langle z,g\rangle|$.
Every literal concerns the unchanged $g$, and both guards just checked
hold. Hence both are actual members of the entire enlarged fiber.
The only changed physical original leaf lies at depth $k+1>h$, so
their replies agree through $h$, including all absent replies at those
depths. All three target cuts are reached with the same complete
outside. Their partitions are respectively
$\{\{1,2\},\{3\}\}$ and $\{\{1\},\{2\},\{3\}\}$: $z,z'$ have
height $k>m$ and cannot equal $g$, and $z'\ne z$.

For completeness, the operational implication used here is the
presentation-independent finite-reply-tree and locality direction of
[ARH, (2.3)][ARH]. A source-total comparator with a uniform read bound
has finitely many reachable reply prefixes, and hence finitely many
submitted physical words, by the unrolling argument of Theorem 4.2.
Let $h$ bound their lengths. Agreement of original replies through $h$
is preserved through every iterate of $\rho$: original branch nodes
persist, and an original leaf met within the prefix has the same label
and thus the same expanded image. Induction on the iterate proves this
locality without a bound on the number of updates. The pair (GRS.31)
therefore follows the same actual replies, choices and halt in the
comparator and receives the same output, a contradiction. This proves
the exclusion for EVERY comparator, not just a chosen finite menu.

The physical root is always a branch on $U_m^-$ too. Deleting its
constant reads gives $q\le\ell$ on each source, so a finite uniform
length bound would imply a finite uniform read bound. Finally the paid
original traversal in Corollary 5.3 works on every finite source of
(GRS.30). Its lack of uniform bounds is consistent with sourcewise
termination. $\square$

The two-source reduction in Proposition 7.1 makes the task artificially
cheaper; removing the acquired equation in Theorem 7.2 enlarges the
fiber and destroys uniform finite recovery. They are opposite changes
of domain. Neither is licensed by preserving only a list of output rows
or by treating two physical copies as independent.

## 8. Information, whitebox use and the boundary of transfer

**Proposition 8.1 (what a retained whitebox summary must preserve).** Fix
the actual operations and full-row target of Definition 1.3. A summary
of an acquired input cannot determine its exact feasible budget region
if it identifies $U_m$ with the representative domain in Proposition
7.1 while retaining only their identical set of possible rows. Nor can
it identify the coupled $U_m$ with $U_m^-$ and retain its uniform finite
recovery answer.

Proof. In the first case the common row set has two elements but the
two exact budget regions have different minimal vectors, by Theorem
6.3 and Proposition 7.1. In the second case the finite feasible region
is nonempty for $U_m$ and empty for $U_m^-$, by Theorems 6.3 and 7.2.
A function of the same summary has the same value on both inputs and
cannot equal both different answers. $\square$

For a machine-learning or whitebox interpretation, the precise lesson
is about what a model is asked to retain and which observations it can
actually acquire. Knowing the finite list of output classes does not
specify the cost of certifying an output on all states compatible with
the actual record. Here that cost grows like the number of independent
leaf alternatives, although the output remains binary and the hidden
tree size is unbounded. An acquired cross-version equation can eliminate
an unbounded comparison obligation without disclosing the unknown tree.
The equation's acquisition, certification and retention remain paid.

Constructive counterpairs have a concrete diagnostic use: on the
accepting source they identify a particular unexamined cone in which a
different admissible source would receive an incorrect row. After
deleting the graph record, pairs exist beyond every finite original
prefix. These are exact model-relative failure certificates. They are
not training data with a claimed distribution, a guarantee about
generalization, a learned-policy construction, an empirical gain, or a
claim of reduced physical energy. There is no generic risk-decomposition
argument substituting for the source/action proofs above.

The graph theorem does not settle exact resource synthesis on the entire
constructor-elimination family $\mathcal E_{\rm CE}$ of ARH19–25.
That larger question remains open here. Its parameter occurrences need
not have the simple two-copy, one-shared-suffix form (GRS.7). A proposed
extension must establish common physical actions before all sources,
preserve each entire domain, and provide whole-row terminal formulas
and an unbounded-address negative stopping argument for its own
representation. Failure to prove that bridge is not an impossibility
theorem for $\mathcal E_{\rm CE}$.

There are specific existing warnings against automatic transfer.
[SRF, Counterexample 1.6][SRF] disproves recognizability of a particular
direct same-root convolution of a physical word and a shifted residual
tree; it does not disprove another encoding. [TPO, Definition 1.2 and
Corollary 4.2][TPO] excludes a uniform native normal-domain definition
in its named four-sort covariant term-power language with pointwise
inner formulas and no variable leaf-address selector. It says nothing
against the full binary-position finite-set interpretation in Lemma
2.2. Neither obstruction is promoted to general resource-synthesis
impossibility. The concrete impossibility established here is exactly
the acquired-relation-deletion theorem on (GRS.30).

## 9. Suppliers, mathematical delta and evidence boundaries

**References 9.1 (bounded comparison and exact reuse).** The project
comparison is against the immutable source collection at
[`124cd13b334f992a6dcee980a5527e0dbfe4492e`][BASE]. The following are
the precise suppliers and boundaries used in this volume.

| Source | Supplied result and scope of use |
| --- | --- |
| [ARH, §§1–3, Theorem 8.2, §§27–32][ARH] | Exact paid acquired graph and complete-state cut; both original-source inclusions; entire arbitrary-$H_0,Q$ determining-prefix decision, finite bad pairs at every depth, and sufficient static budgets. The source already gives existence on this complete family. It expressly leaves minimum resources open. |
| [SRF, entire volume, especially §§1–3][SRF] | Exact resources on the complete synchronous family; fixed-epoch finite-set reply formula, source/action interpretation obligations, prefix-to-whole-row labels, finite control, Pareto and separate same-run methods. Its synchronous premise is not asserted for arbitrary graph targets. Its §4 consumer is a one-leaf alternative in a different four-hole fiber; it is not (GRS.21). |
| [ABC, Proposition 6.4 and Definition 8.1][ABC] | Same-source nonexpansive epoch-five cap and cleanup on acquired signed fibers, and conditional cofinality after a static supplier. These operational hypotheses are matched in Lemma 5.1. ABC8.1 states, but does not itself discharge for this graph, the common-address-before-universal-source decision obligation. |
| [JRF, §§4–7][JRF] | Finite-control equivalence, exact finite-length tests, cofinal Pareto construction and separate rational weighted optimization, including zero weights. Their methods are attributed suppliers; their literal-only source predicates are replaced by (GRS.10)–(GRS.15), with both operational directions proved. |
| [SCR, §§9–10][SCR] | Epoch-four raw normalization with an additive address estimate. It is not used as joint sourcewise domination or substituted for the nonexpansive epoch-five cap. |
| [SLH, Theorem 2.2, §§55, 59–62, 74][SLH] | Paid original-node decoder, complete old rows and leaf certificates on all finite comparison trees. SLH55.3 supplies the static upper certificate in Theorem 6.3; the adaptive two-copy packing lower bound is proved here. |
| [AOF, Assumption 1.1 and §§2–5][AOF] | Exact resources on the acquired whole-root/proper-descendant certificate family. Its orbit promise is not imposed on the present graph and does not supply this theorem. |
| [TPO, Definition 1.2, Corollary 4.2, Proposition 5.2][TPO] | A language-specific all-shape normal-domain and canonicalization obstruction. Its scope is kept in §8; it supplies no general impossibility conclusion about the graph or $\mathcal E_{\rm CE}$. |
| [Nils Klarlund and Anders Møller, *MONA Version 1.4 User Manual*, January 2001, §§7.1–7.2, printed pp. 39–40][MONA] | Primary `literature-attested` supplier: positions in the infinite binary successor tree, finite sets, fixed successor strings, and WS2S decidability by ordinary finite bottom-up tree automata. Page 39 states validity decision and counterexamples; page 40 defines the transitions via the one-state-space guided special case. This supplies logical decision only after Lemma 2.2 and the explicit source/action/terminal interpretation. |

The primary PDF is identified by SHA-256
`392974616c46d86d7225cf5c12f76e14b5da3a1f37fd1e7b00e97d9e0095d444`.
Its printed pages 39–40 are PDF pages 41–42. The formulas here use
ordinary two-valued WS2S; MONA's optional restrictions with a third
“don't-care” value are not used. No solver execution, implementation,
complexity estimate or broader automata closure is asserted.

The `repo-derived` delta is the complete graph's shared-source physical
action interpretation (GRS.7)–(GRS.10), its exact full-row resource
decision after the supplied graph gate, and the scalable whole-fiber
separation (GRS.25)–(GRS.31). Generic finite games, automata decisions,
prefix labels, normalization, cofinal grids, Pareto order and rational
threshold optimization are supplied methods, not new knowledge claimed
by this manuscript. Graph parameterization and ARH's nested comparison
classification are supplied results too.

Merely restating ARH existence, wrapping SRF, or presenting a finite
menu without the two directions of Theorem 4.2 would add no proved
resource bridge and would not justify another volume. The mathematical
reason for this volume, compared with no new publication, is the
completed source/action/whole-row correspondence on the entire named
graph and the quantitative whole-fiber counterexample to row sampling.
This is a bounded source-relative comparison, not a global originality,
priority or absence-of-literature claim. The primary literature check is
limited to the stated MONA interface; no other primary theorem is
silently imported as an unproved constructor-offset closure.

**Authorship and verification boundary.** The construction and exposition
are those of an independent CLI mathematical author with repository
priors exposed. The formal-thinking-and-answer and theory-volume-template
conventions are applied within the explicit pure-theory scope. The
proofs are ordinary deductions with their supplier hypotheses stated;
they do not claim sterile context, statistically independent priors,
independent review, Lean verification or implemented-solver validation.
Source identity and manuscript checks do not certify the mathematics.

No result refunds acquisition or certifies physical realization. Outputting
the row does not erase the acquired graph, old literals, new replies or
other accessible state. Any later complete retention cut and new entry
need their own actual state correspondence and payment. Exact resources
for general guarded coupled histories, for the entire
$\mathcal E_{\rm CE}$, and for other computational or physical interfaces
remain outside the proved conclusions. These results form a finite
mathematical unit, not completion of the continuing research programme.

[BASE]: https://github.com/the-omega-institute/trureturing/tree/124cd13b334f992a6dcee980a5527e0dbfe4492e
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SRF]: RECURSIVE_RELATIONAL_OBSERVATION_SYNCHRONOUS_RESOURCE_FRONTIER.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[SCR]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[MONA]: https://www.brics.dk/mona/mona14.pdf

## 追加锚（本行以下为增补区）
