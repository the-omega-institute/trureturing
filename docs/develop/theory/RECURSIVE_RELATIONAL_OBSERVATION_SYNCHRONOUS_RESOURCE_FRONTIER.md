# Synchronous relational fibers and the complete resource frontier

This volume treats the entire acquired family $\mathfrak S$ of
[ARH, Definition 10.2][ARH], under its actual acquisition, complete access
cut and nonempty-source hypotheses. Every old occurrence, repeated class,
old inequality, signed mixed-epoch record and both endpoint guards remain
imposed. Empty and root cuts, ground charts and zero-coordinate charts are
included. The target remains the whole original $R_Q(u)$: concrete outside,
reached positions in occurrence order, and full equality partition.
The results are ordinary mathematical deductions, not kernel verification.

## 1. Common physical words and complete rows

**Definition 1.1 (services, costs and two depths).** Fix the acquired input,
its entire source fiber $U\ne\varnothing$, and certified entry epoch $N$
from [ARH, Assumption 1.3][ARH]. A service is deterministic, effective and
terminates correctly on every $u\in U$. Its source operations are actual
original-root $\mathsf{Read}(p)$ at arbitrary finite words, forward actual
$\mathsf{ApplyRho}$, and absorbing $\mathsf{Halt}$. Local work uses the
common initial state and acquired replies only. No chart, source identity,
unknown-tree equality, membership, reset, cloning or reroot port is added.

Write

$$
 c_A(u)=(q_A(u),d_A(u),\ell_A(u)),\qquad
 \ell_A(u)=\sum_{\text{actual reads }p}|p|.
\tag{SRF.1}
$$

Every call, including repetitions and absent replies, is counted. All three
costs precede any supremum. Installation, address construction, memory,
local work, acquisition, certification, physical time and energy are
separate resources. Use $h_0$ for the common original pattern depth called
$d$ in [ARH, Definitions 3.1 and 10.1][ARH]; use $d$ here for a bound on
post-entry updates. These two parameters are unrelated.

**Definition 1.2 (a chart-independent routing tree).** Let $a_i$ be every
reached old-hole occurrence in the known outside context $C$, and $b(i)$
its old class. Construct a finite full binary routing tree $K$ by replacing
each hole of $C$ by the complete binary skeleton of depth $h_0$. Its leaf
addresses form $B$: the concrete outside-leaf addresses of $C$, together
with all $a_i s$ for $|s|=h_0$. Its internal addresses form $I$. The tree
$K$ is a finite syntactic routing device, not an observation of the source.

Every finite physical word has exactly one of the forms

$$
 p\in I,\qquad\text{or}\qquad p=c z\quad(c\in B),
 \qquad |p|=|c|+|z|.
\tag{SRF.2}
$$

Indeed follow its letters in the finite full tree until the word ends at
an internal node or first meets a leaf. Fullness and prefix-freeness of
$B$ give existence and uniqueness. If $C$ is a root hole, $B$ is level
$h_0$; if there are no old holes, $K=C$ with its concrete leaves treated
as routing leaves. A one-leaf $C$ gives $B=\{\varepsilon\}$ and $I=\varnothing$.
All physical prefixes are retained, including longer occurrences of a
repeated old class; no shortest-occurrence normalization is used here.

**Lemma 1.3 (exact routing across every original chart).** Fix a chart
$\eta$ of [ARH, Proposition 10.3][ARH] and an epoch numeral $e\ge0$.
For $p\in I$, the reply at $p$ in $\rho^e W_\eta[v]$ is a computable
constant independent of $v$. For every $c\in B$, precisely one of the
following descriptions applies, uniformly over feasible $v$:

1. If $c=a_i s$ and the class pattern reaches its depth-$h_0$ frontier at
   $s$, let $x$ be that frontier variable. Then
   $r_{\rho^e W_\eta[v]}(cz)=r_{\rho^e v(x)}(z)$ for every finite $z$.
2. Otherwise a known original leaf $\lambda\in\{\alpha,\beta\}$ occurs
   at an address $a$ with $c=a t$, where $t$ is fixed. Put
   $g=(\rho^e\lambda)|_t$ if that subtree exists, and $g=\varnothing$
   otherwise. Then $r_{\rho^e W_\eta[v]}(cz)=r_g(z)$ for every $z$, where
   the empty tree has reply absent everywhere.

The finite choice of routing form and the suffix $z$ specify one common
physical action before the chart or source is quantified; its charged
length is exactly (SRF.2), even in case 2.

Proof. ARH uses the same original depth $h_0$ in every chart. Every
frontier variable has an original occurrence $a_b s_x$ with
$|s_x|=h_0$, and all occurrences of a class contain the same original
subtree. Thus a routing leaf in an old hole either reaches that very
frontier variable, or its length-$h_0$ path has already met a concrete
leaf of the pattern. An outside routing leaf is itself concrete and has
$t=\varepsilon$. These are exhaustive, including patterns that terminate
earlier and ground charts. The iterate $\rho$ preserves each original
pairing node and replaces each original leaf by its known finite image.
Induction along the fixed original path proves both displayed reply
identities, including descendants born inside that image and paths that
remain absent. If $p\in I$, it meets no residual variable: every residual
occurrence is a leaf of $K$. Navigation therefore either ends at an
explicit original pairing node or enters a known finite leaf image, so
its reply is constant on the chart.

The routing data $K,I,B$ depend only on the common old row and $h_0$,
not on $\eta$. A suffix is neither deleted from an unknown tree nor
chosen after seeing a chart. At execution the word $cz$, including its
whole prefix, is submitted at the original root. Repeated occurrences
select the same residual coordinate in each chart, by the old-class
source identity just cited. The argument is valid simultaneously for
all charts and all satisfying valuations, without weakening any of
$D_\eta$'s joint constraints. $\square$

**Lemma 1.4 (an aligned finite-set interpretation).** For any finite
skeleton shape and fixed epoch and routing annotations, its physical
reply predicates and each exact $D_\eta$ have effective WS2S formulas.
Their suffix variables range over arbitrary finite words. Their source
variables range over complete arbitrary finite trees, including arbitrary
continuations below every suffix marker.

Proof. Work in the binary successor tree $\{L,R\}^*$, with root
$\varepsilon$, and use ordinary two-valued WS2S. Represent a residual tree
$x$ by three finite sets $X_\alpha,X_\beta,X_{\mathsf{branch}}$. Require
them disjoint, their union $T_X$ to contain the root, every nonroot member
to have a parent in $X_{\mathsf{branch}}$, each branch to have both
children in $T_X$, and no leaf to have a child in $T_X$. These formulas
are exactly the nonempty finite ordered-tree condition: repeatedly taking
parents reaches the root, and the child conditions give full branching.
They exclude disconnected islands and allow every finite source tree.
Use one such triple for each distinct residual variable, not one for
each occurrence. Coordinate domains can overlap in this common suffix
universe; they are not independent feasible languages.

Conjoin the tree-validity formulas just given into $D_\eta$. For its
remaining conditions, take its supplied exact automaton from
[ARH, Lemma 11.2][ARH]. The union of the coordinate domains is exactly its
padded convolution domain; positions used only to name markers are not
inserted into that domain. Existentially quantify a finite state set for
each automaton state, partition this union into those sets, impose its
finite transition disjunction at every node with the actual coordinate
labels and padding, and require an accepting root state. At a binary
union node use both child states; at a nullary node use a nullary
transition. This is an explicit WS2S run formula, equivalent to acceptance
in both directions. It retains all disequalities and signed guards already
compiled into $D_\eta$. Zero-coordinate charts instead have their computed
constant feasibility truth; no empty tuple automaton is presumed.

There is also a direct reply formula that needs no general transducer
closure. For a fixed $e$, expand the two finite trees $\rho^e\lambda$.
For $r\in\{\alpha,\beta,\mathsf{branch}\}$ set

$$
\begin{aligned}
\mathsf{Reply}_{e,r}(X,z)\quad\Longleftrightarrow\quad&
 [r=\mathsf{branch}\ \land\ z\in X_{\mathsf{branch}}]\\
 &\lor\!\bigvee_{\substack{\lambda\in\{\alpha,\beta\},\ t\in\operatorname{Pos}(\rho^e\lambda)\\
                             r_{\rho^e\lambda}(t)=r}}
 \exists y\ (y\in X_\lambda\ \land\ z=y t).
\end{aligned}
\tag{SRF.3}
$$

Here each $t$ is a fixed literal word, so $y t$ is a finite composition
of successor symbols, not concatenation of two variable words. Define
$\mathsf{Reply}_{e,\mathsf{absent}}$ as the complement of the three
nonabsent replies. The domain of $\rho^e x$ consists exactly of its
preserved original branch nodes and the finite images rooted at original
leaves. These parts are disjoint. This proves (SRF.3), its absent case and
uniqueness of the reply for every $z$, including $e=0$ and $z=\varepsilon$.
For a fixed ground $g$, the nonabsent reply formula is just the finite
disjunction $\bigvee_{t:r_g(t)=r} z=t$; for $g=\varnothing$ it is false.
Lemma 1.3 now supplies each chart's formula for the same physical word.

Crucially, the complete source sets and the automaton's run sets are
quantified without a depth restriction depending on the markers. A marker
$z$ may lie above, inside or below a source tree. If it lies at an original
branch, its children and every deeper source constraint are still present
in $T_X$ and in the run formula. If it lies beyond the source, the finite
leaf-image terms decide born versus absent. Thus a marker-only truncation
of the convolution is not being used. At no step is a relation
$z=cw$ between two variable address tracks needed: the physical prefix
$c$ has been handled by the finite routing annotation, while (SRF.3)
only appends a fixed template word to $y$.

WS2S permits Boolean operations and quantification over all finite sets
and all binary-tree positions, and has an effective decision procedure;
[MONA, §§7.1–7.2, pp. 39–40][MONA] gives precisely these interfaces.
Consequently every finite combination of the displayed formulas is an
actual decidable sentence. The run encoding above specifies why the
supplied source automata enter that language; no assertion about arbitrary
constructor offsets is a premise. $\square$

**Proposition 1.5 (exact whole-row labels across charts).** If the positive
branch of [ARH, Theorem 14.1][ARH] supplies an original determining depth
$H$, one can compute the exact finite image $\mathscr R=R_Q(U)$ and formulas
$\mathsf{Row}_{\eta,r}(X)$, $r\in\mathscr R$, that partition the feasible
valuations in each chart by their complete row. Equal rows from different
charts or different prefixes have the same label.

Proof. List all reply vectors $\theta$ on the finitely many original
words of length at most $H$. For every chart form

$$
 C_{\eta,\theta}(X)=D_\eta(X)\ \land\!
 \bigwedge_{|p|\le H}
     [r_{W_\eta[X]}(p)=\theta(p)].
\tag{SRF.4}
$$

These fixed-word predicates use Lemmas 1.3–1.4 with $e=0$; impossible
prefix vectors cause no problem. Decide each cell's exact emptiness.
For a nonempty cell extract a finite tuple witness, or enumerate finite
tuples until one satisfies the decidable concrete constraints, after
nonemptiness has been decided. In a zero-coordinate chart test its one
empty valuation. Fill $W_\eta$ and compute the witness's entire row.

Every feasible valuation belongs to exactly one such prefix vector.
If two feasible valuations have the same $\theta$, even in different
charts, their actual sources agree through $H$, so the supplied
$\operatorname{PrefDet}(U,Q,H)$ makes their entire rows equal. The witness
row therefore classifies the whole cell. Take all nonempty cell rows,
compare their finite concrete outside terms, reached positions in order
and equality partitions, and merge literal-equal whole rows across the
entire chart list. Their set is $\mathscr R$. Define
$\mathsf{Row}_{\eta,r}$ as the disjunction of exactly the cells in that
chart whose computed row is $r$. Every actual source lies in one chart
by ARH Proposition 10.3, proving both that these labels exhaust $R_Q(U)$
and that every reported row is attained.

For two charts, full-row equality is now exactly

$$
 \bigvee_{r\in\mathscr R}
   \mathsf{Row}_{\eta,r}(X)\land\mathsf{Row}_{\zeta,r}(Y).
\tag{SRF.5}
$$

The witnesses certify exact feasible cells; they are not a guessed finite
source sample. Neither $\eta$ nor $\theta$ is observed by the service.
Only a terminal label is installed. ARH Proposition 12.1's
$\mathsf{Bad}_\eta$ compares two valuations within one chart and is used
by the supplied prefix decision, not as a cross-chart terminal test here.
In particular, constant rows in individual charts do not justify a common
root halt unless their labels merge to one row. $\square$

**Counterexample 1.6 (the direct physical-word convolution is different).**
A finite constructor context does not make a physical-word track and a
residual tree track recognizable in their direct same-root convolution.
An input in $\mathfrak S$ already demonstrates the obstruction. Take
$P=Q=\{L\}$, outside $\langle\square,\alpha\rangle$, one old class,
empty histories and $N=0$. Its common depth is $h_0=2$, and one chart is
$W[y,x]=\langle\langle\alpha,\langle y,x\rangle\rangle,\alpha\rangle$.
Take its fixed section $y=\alpha$ and abbreviate it by $W[x]$. This
section retains arbitrary $x$; the frontier at relative $RL$ has merely
been fixed to a ground value. Let $C_0=\beta$ and
$C_{n+1}=\langle\alpha,C_n\rangle$. For $n,m\ge1$,

$$
 r_{W[C_n]}(L R^{m+2})=\beta\quad\Longleftrightarrow\quad n=m.
\tag{SRF.6}
$$

Proof. Fixing the $y$ coordinate to $\alpha$ is a finite-state template
restriction; it contributes no domain below the root of the residual
convolution. A recognizer for the full chart relation would therefore give
one for this section by fixing and dropping that coordinate. The $x$
residual occurs at $LRR$, leaving suffix $R^m$. In a direct
same-root convolution of the physical path and $C_n$, the left branch
contains the path continuation depending on $m$, while the right branch
contains $C_{n-1}$ and no path continuation. In a deterministic finite
bottom-up automaton two distinct $n,k\ge1$ give the same state on those
right subtrees. Replace just that subtree in the accepted $n=m$ diagonal
instance. The result is a valid convolution with residual $C_k$ and the
unchanged physical word $LR^{n+2}$, accepted with the same root state,
contradicting (SRF.6). Determinization gives the same contradiction for
nondeterministic recognizability.

In Lemma 1.3 the header is instead the fixed $c=LRR$, the marker is
$z=R^m$, and (SRF.3) with $e=0$ tests $z\in X_\beta$. Its physical length
is $3+m$. Both unbounded parts are now at the same suffix coordinates.
This is an actual change of representation with the common-word proof
above, not a closure claim for the direct encoding. $\square$

## 2. Exact operational correspondence on every $\mathfrak S$ input

**Definition 2.1 (finite adaptive certificates).** A $(q,d)$ skeleton is
a finite tree with read depth at most $q$. An internal node $v$ has four
reply children and a chosen epoch $e_v\in\{N,\ldots,N+d\}$, nondecreasing
along paths. It has either a fixed address in $I$, or a fixed header
$c_v\in B$ and one suffix variable $z_v$. A leaf is an absorbing halt
labelled by a member of $\mathscr R$ when that image has been computed.
No actions are appended to a halt. Execution performs the actual epoch
differences and submits the actual word from (SRF.2).

For a leaf $t$, let $\mathsf{Path}_{\eta,t}(X;\mathbf z)$ be the conjunction
of its actual edge-reply formulas from Lemma 1.4. Its counts are
$k_t$, the number of read ancestors, and $d_t=e_{\rm last}-N$ (zero for
root halt). Its submitted-length sum is

$$
 L_t(\mathbf z)=
 \sum_{\substack{v\prec t\\p_v\in I}}|p_v|
 +\sum_{\substack{v\prec t\\c_v\in B}}(|c_v|+|z_v|).
\tag{SRF.7}
$$

A leaf's exact reachability predicate is

$$
 E_t(\mathbf z)=\bigvee_\eta\exists X\,
       [D_\eta(X)\land\mathsf{Path}_{\eta,t}(X;\mathbf z)].
\tag{SRF.8}
$$

Ground charts contribute their constant-source path predicates. Empty
paths mean true. Unreachable leaves have no execution cost.

**Theorem 2.2 (bounded reads and updates, with unbounded addresses).** For
every legally acquired nonempty $\mathfrak S$ input and every $q,d\in\mathbb N$,
it is decidable whether a legal source-total service satisfies
$\sup_Uq_A\le q$ and $\sup_Ud_A\le d$. A positive decision constructs one.
The decision covers arbitrary original physical addresses, arbitrary
pointwise finite local work, adaptive updates and variable absorbing halt.

Proof. First apply ARH Theorem 14.1. If no determining prefix exists,
ARH equation (2.3) excludes every uniform finite read service, so the
answer is no. This includes the negative inputs without attempting to
construct finite whole-row labels there.

On the positive branch construct $\mathscr R$ and its formulas by
Proposition 1.5. Enumerate the finitely many skeleton shapes, epoch
annotations, routing forms and leaf labels of Definition 2.1. For each,
decide the following WS2S sentence:

$$
 \exists(z_v)_v\quad
 \bigwedge_\eta\ \forall X\quad
 \left[D_\eta(X)\Longrightarrow
   \bigwedge_t\bigl(
     \mathsf{Path}_{\eta,t}(X;\mathbf z)
       \Longrightarrow\mathsf{Row}_{\eta,r_t}(X)\bigr)\right].
\tag{SRF.9}
$$

There is a quantifier only for a node having a suffix. All its suffixes
are chosen before every chart's universal source quantifier; sharing the
same variable at one control prefix is essential. The source quantifiers
range over complete finite trees of arbitrary size. The logical
decidability in Lemma 1.4 supplies a negative stopping rule, independently
of any address menu or length bound. A positive sentence has a finite
suffix tuple: extract it from a model or enumerate finite tuples and
decide the remaining fixed-tuple sentence until a witness is found.
Enumeration is used only after a positive decision. For $q=0$, (SRF.9)
requires one label valid on every feasible chart, exactly the zero-read
whole-row condition.

For sufficiency, install those physical words, epochs and full labels.
Every actual source has exactly one feasible chart valuation. Lemma 1.3
and (SRF.3) imply, by induction on actual replies, that its physical run
satisfies the corresponding path formula. It therefore halts with its
whole row by (SRF.9). This is a finite effective source-total program
within the two budgets. It executes no chart or prefix oracle, and its
cost at a reached leaf is exactly $(k_t,d_t,L_t)$.

For necessity, take any permitted comparator within the two budgets.
At a reachable reply prefix, its common control and previous replies
fix all subsequent local computation and actual updates until its next
read or output. That segment is finite because some actual source reaches
it and the comparator is source-total. There are at most
$1+4+\cdots+4^q$ reply prefixes. Unroll these segments, retain every
reachable read with its actual physical word and epoch, retain each early
halt, and put an immediate halt at every unreachable child. Delete
updates after the last read: they yield no information under the service
contract and the same output can be computed before them. This decreases
only the update cost. No claim of extracting this tree effectively from
arbitrary source-total code is needed for necessity.

Factor each of the finitely many actual words by (SRF.2). All fit the
finite routing forms with their exact original lengths, regardless of
which charts reach them. Correctness makes every reachable halt's
output one member of $\mathscr R$. Choose that label, and any member
for an unreachable halt; $U\ne\varnothing$ makes $\mathscr R$ nonempty.
The resulting skeleton is among the enumerated ones and satisfies
(SRF.9) on all feasible chart valuations. Thus every original comparator
is included. This argument assumes no uniform prior bound on local work,
source size or address lengths. $\square$

**Corollary 2.3 (finite length bounds and exact path witnesses).** One can
also decide every triple of finite upper budgets $(q,d,L)$ and construct
a service when feasible. For an extracted skeleton, exact reachability,
all worst-coordinate costs and every same-run weighted maximum are
computable, with actual sources attaining each nonempty path cost.

Proof. For the triple decision enumerate physical words of length at
most $L$ and the finite skeletons; impose (SRF.9), and require $L_t\le L$
only for reachable leaves, using (SRF.8). A comparator with total length
at most $L$ uses only such words on reachable reads, and its unreachable
children can be replaced by immediate halts, so necessity loses nothing.
Every passing skeleton has the asserted actual costs by Theorem 2.2.
This finite-length test is separate from the unbounded-address negative
stopping rule in that theorem; no general WS2S predicate comparing variable
word lengths is asserted.

With all words fixed, decide (SRF.8) for each leaf and extract a satisfying
chart tuple when nonempty. Filling its source term gives an actual member
of $U$ attaining $(k_t,d_t,L_t)$. Maximize each coordinate over these
leaves, or first form a weighted sum at each leaf and then maximize.
Different coordinate maxima need not share a witness. $\square$

## 3. Complete Pareto basis and same-run weighted prices

**Definition 3.1 (the supplied cofinal rectangle).** On the positive branch
of ARH Theorem 14.1, compute a sufficient static upper budget
$(K_0,0,L_0)$, for example using (ARH.14.2) and multiplying its read bound
by its maximum physical address length. Set

$$
 K=\max\bigl(K_0,L_0+\max(0,2-N)\bigr),\qquad
 U_N=\max(N,5)-N.
\tag{SRF.10}
$$

[ABC, Proposition 6.4 and Definition 8.1][ABC] already supply the
same-source cap and cleanup on the entire signed fiber. The cap preserves
$q$, makes $d'=\min(d,U_N)$ and does not increase $\ell$; cleanup does
not increase any coordinate and gives $q\le\ell+\max(0,2-N)$. These
are reused operational results. The epoch-four transport of SCR has an
additive address bound and is not substituted for this joint cap.

**Theorem 3.2 (effective complete joint upper-budget Pareto basis).** Let
$\mathcal F_S\subseteq\mathbb N^3$ be all finite upper-budget triples
attainable on the entire acquired $U$. If the prefix decision is negative,
$\mathcal F_S=\varnothing$, and every correct service has unbounded worst
read count and unbounded worst submitted-length sum. If positive, one can
compute a finite nonempty set $\mathcal B_S$ with

$$
 \mathcal F_S=\{b\in\mathbb N^3:\exists v\in\mathcal B_S, v\le b\},
 \qquad \mathcal B_S=\operatorname{Min}(\mathcal F_S),
\tag{SRF.11}
$$

and construct a service with exact worst vector $v$ for every
$v\in\mathcal B_S$.

Proof. The finite optimization is [JRF, Lemma 5.2 and Theorem 5.3][JRF]
with the following exact supplier replacement. Its source domain is the
whole $U$ of ARH, its read/update coordinates are $q,d$, its third
coordinate is (SRF.1), its static upper budget is Definition 3.1, its
operational cap is ABC Proposition 6.4, and its two decision procedures
are Theorem 2.2 and Corollary 2.3. No literal-only `Adm/SameRow` routine
is applied to the signed input.

For explicit termination, first decide every pair
$0\le q\le K$, $0\le d\le U_N$ with addresses unbounded, by Theorem 2.2.
For each true pair extract a skeleton and its finite worst length
$L^{\rm wit}_{q,d}$. Only then use Corollary 2.3 in the finite interval
$0\le L\le L^{\rm wit}_{q,d}$ to find the least feasible $L_{q,d}$.
Take the coordinatewise minimal retained triples $(q,d,L_{q,d})$.
False pairs never trigger an unbounded search for addresses.

To check cofinality, normalize any finite-budget comparator with the
supplied cap and cleanup. Write its resulting worst read and length
costs as $q',L'$. They satisfy $q'\le L'+\max(0,2-N)$. If $q'\le K$,
its pair is in the grid, whose least length is no greater than $L'$.
If $q'>K$, then $q'>K_0$ and $L'>L_0$, so the sufficient static service
is no worse in every worst coordinate. This compares coordinate maxima,
not costs on each same source. The grid is therefore cofinal. Conversely
every retained triple is feasible by the constructed skeleton. These two
inclusions give (SRF.11). At a minimal triple the witness's actual worst
vector cannot be strictly smaller, because that vector would itself be
feasible. Exact maxima have actual-source witnesses by Corollary 2.3.

On a negative prefix decision, ARH equation (2.3) excludes finite worst
reads. If any correct service had finite worst length $L$, the supplied
cap and cleanup would give a correct uniform read bound
$L+\max(0,2-N)$, a contradiction. A pointwise total static traversal still
attains the extended vector $(\infty,0,\infty)$; unbounded worst costs do
not mean an infinite execution on a finite source. $\square$

**Theorem 3.3 (every rational same-run weighted minimax value).** For
$\lambda=(\lambda_q,\lambda_d,\lambda_\ell)\in\mathbb Q_{\ge0}^3$, put

$$
 W_\lambda(A)=\sup_{u\in U}
   (\lambda_q q_A(u)+\lambda_d d_A(u)+\lambda_\ell\ell_A(u)),
 \qquad W_\lambda^*=\inf_A W_\lambda(A).
\tag{SRF.12}
$$

If $\lambda_q=\lambda_\ell=0$, the value is zero on every input. If
$\lambda_q+\lambda_\ell>0$ and the prefix decision is negative, the value
is infinity. On a positive prefix decision the value is a computable
finite rational, attained by an actual finite service, with an actual
source attaining its worst weighted cost. All zero-weight faces remain
in scope.

Proof. Use the methodology of [JRF, Theorem 7.1][JRF], now with the proved
source and action interfaces of §2. First, on any input, the static
historical decoder of [SLH, Theorem 2.2][SLH] can traverse the whole
original tree: decode its root, recurse on original children only after
a branch, and stop at its original leaves. This terminates on each finite
source using only actual reads at epoch $N$. It computes the whole
original row and uses zero updates. Thus update-only and all-zero prices
are zero even when no uniform read budget exists. In the negative branch,
Theorem 3.2's separate unbounded read and length costs make every weighted
supremum infinite if either coefficient is positive. The pointwise
static service realizes that extended value.

On the positive branch the static supplier gives
$B_0=\lambda_qK_0+\lambda_\ell L_0$. If only updates are priced the same
static supplier suffices, so assume $\lambda_q+\lambda_\ell>0$.
ABC's cap and cleanup decrease each same source's cost vector; hence they
do not increase (SRF.12), even when an unpriced coordinate was initially
unbounded. Updates can be bounded by $U_N$. If $\lambda_q>0$, every
candidate with value at most $B_0$ has read bound
$k_\lambda=\lfloor B_0/\lambda_q\rfloor$. If
$\lambda_q=0<\lambda_\ell$, put
$L_\lambda=\lfloor B_0/\lambda_\ell\rfloor$ and use cleanup to obtain
$k_\lambda=L_\lambda+\max(0,2-N)$.

For a threshold $z\in[0,B_0]$ enumerate the finitely many shapes and
epochs under these bounds and require correctness (SRF.9) and

$$
 E_t(\mathbf z)\Longrightarrow
 \lambda_q k_t+\lambda_d d_t+\lambda_\ell L_t(\mathbf z)\le z
 \quad\text{at every leaf }t.
\tag{SRF.13}
$$

The suffix tuple in this display is distinguished from the scalar
threshold by its boldface. If $\lambda_\ell>0$, each reached word has
length at most $\lfloor B_0/\lambda_\ell\rfloor$, so enumerate those
finite literal words and test the numerical inequality only at reachable
leaves. If $\lambda_\ell=0$, then $\lambda_q>0$ and the left-hand cost
is independent of suffixes. For every numerically over-budget leaf add
$\neg E_t(\mathbf z)$ to the WS2S sentence, inside the existential suffix
quantifiers. This is a decidable unbounded-address test. It requires no
variable-length comparison in WS2S and never charges an unreachable leaf.

The normalization and unrolling include every original service of value
at most $B_0$, with no increase of its same-run sum. Conversely each
passing skeleton executes precisely the costs in (SRF.13) on its actual
source. These are the two threshold directions. Choose a positive common
denominator $a$ of the weights. Every finite run sum belongs to
$a^{-1}\mathbb N$; a bounded nonempty set of such sums has a maximum
on the same lattice. Test $0,1/a,\ldots,B_0$ in order. The static supplier
ensures a true test, and the first true threshold is the exact attained
minimum. Corollary 2.3 gives its worst-source witness.

This procedure does not minimize a weighted sum of the three separate
coordinate maxima, nor restrict an unpriced, unbounded service class
without the stated sourcewise domination argument. $\square$

## 4. An exact sharpening of the entire ARH16.1 fiber

**Theorem 4.1 (sharp full-fiber consumer).** Retain all of
[ARH, Proposition 16.1][ARH]'s acquired input:

$$
\begin{gathered}
P=\{LL,LR,RL,RR\},\quad
C=\langle\langle\square_1,\square_2\rangle,
          \langle\square_3,\square_4\rangle\rangle,\quad
\pi=\{\{1\},\{2\},\{3\},\{4\}\},\\
H_0=\{(0,LRL,\mathsf{absent}),(0,RR,\mathsf{branch})\},\\
H_{\rm rel}=\{(0,LL,1,LR,=),(0,RL,1,RR,=),
               (2,LL,0,RL,\ne)\},\\
Q=\{LLL,LLR,RL,RR\},\qquad N\ge2.
\end{gathered}
\tag{SRF.14}
$$

Its entire non-product, non-orbit fiber, supplied by ARH, is

$$
 u_{b,t}=\langle\langle\rho(b),b\rangle,
              \langle\rho(t),t\rangle\rangle,
 \quad b\in\{\alpha,\beta\},\quad t\text{ any finite branch tree},
 \quad t\ne\rho^2(b),
\tag{SRF.15}
$$

subject to all six old inequalities

$$
 \rho(b)\ne b,\quad \rho(b)\ne\rho(t),\quad \rho(b)\ne t,
 \quad b\ne\rho(t),\quad b\ne t,\quad \rho(t)\ne t.
\tag{SRF.16}
$$

Both endpoint guards of every record remain required. Set
$D_N=2+\lfloor N/2\rfloor$. The complete finite upper-budget Pareto basis
and every rational nonnegative same-run price are exactly

$$
 \mathcal B=\{(1,0,D_N)\},\qquad
 W_\lambda^*=\lambda_q+\lambda_\ell D_N.
\tag{SRF.17}
$$

These claims compare with all original adaptive arbitrary-update services.
They sharpen the supplied one-read count by the optimal address length,
joint frontier and same-run price.

Proof. Writing the four old values as $x,b,z,t$, the literals force $b$
to be a leaf and $t$ a branch. The positive records, with their reached
endpoints, force $x=\rho(b)$ and $z=\rho(t)$. The negative record becomes
$\rho^3(b)\ne\rho(t)$, equivalently $t\ne\rho^2(b)$ by injectivity.
The old partition supplies precisely (SRF.16). These implications reverse,
including both guards, so (SRF.15) is the entire fiber. Its eligibility
in $\mathfrak S$, legal paid acquisition and non-product/non-orbit scope
are the supplied ARH16.1 result, not additional restrictions here.

The two supplied whole rows are

$$
\begin{array}{c|c|c|c}
b&\text{reached cuts in order}&\text{outside context}&\text{partition}\\ \hline
\alpha&RL,RR&
\langle\langle\beta,\alpha\rangle,
                 \langle\square_1,\square_2\rangle\rangle&
\{\{1\},\{2\}\}\\
\beta&LLL,LLR,RL,RR&
\langle\langle\langle\square_1,\square_2\rangle,\beta\rangle,
                 \langle\square_3,\square_4\rangle\rangle&
\{\{1\},\{2\},\{3\},\{4\}\}.
\end{array}
\tag{SRF.18}
$$

Indeed in the first case $LL$ is the leaf $\beta$; in the second its
children are the distinct leaves $\beta,\alpha$, each unequal to the two
branch values at $RL,RR$. The retained inequality between those branch
values completes each displayed partition, for every legal $t$.

Put $T_j=\rho^j\alpha$. The known original hole $LR$ currently contains
$T_N$ or $T_{N+1}$. Submit the single physical word

$$
 p_N=LR\,R^{\lfloor N/2\rfloor}.
\tag{SRF.19}
$$

For $N=2m$ the replies are respectively $\alpha,\beta$; for $N=2m+1$
they are $\beta,\mathsf{branch}$. This follows from
$T_j=\langle T_{j-1},T_{j-2}\rangle$ for $j\ge2$ and from
$T_0=\alpha,T_1=\beta$. Thus (SRF.19), of length $D_N$, selects the
whole row (SRF.18) on the entire fiber, with no updates.

For the arbitrary-update lower bound, use the same legal
$t_0=\langle\alpha,\alpha\rangle$ for both $b$ choices. Its image is
$\langle\beta,\beta\rangle$; direct constructor comparison with
$\rho\alpha=\beta$ and $\rho\beta=\langle\beta,\alpha\rangle$ verifies
all six inequalities for both choices. Also $t_0\ne T_2,T_3$, so the
negative record and both guards hold. These two actual sources have the
different rows in (SRF.18).

At any common epoch $N+a$, their root and $L$ are branches, and their
whole $R$ subtrees agree because $t_0$ is common. A distinguishing word
must therefore enter $LR$ or $LL$. In $LR$ it compares
$T_j,T_{j+1}$ with $j=N+a$; in $LL$ it compares them with $j=N+a+1$.
For any suffix of length $r<\lfloor j/2\rfloor$, its edge weight
$w=\#L+2\#R\le2r\le j-2$. All prefixes therefore navigate through
branches of both trees and the two final indices are at least two;
both replies are branch. Hence a distinguishing suffix has length at
least $\lfloor j/2\rfloor\ge\lfloor N/2\rfloor$, and its whole physical
word has length at least $D_N$.

Any correct deterministic source-total comparator must have a first
read whose replies differ on this pair: otherwise common control, local
work, forward updates and halt give the same output. Before that first
difference the actual epoch is common, so the preceding bound applies,
even if the comparator makes arbitrarily many updates or other reads.
Both runs include that read. Thus on a same run $q\ge1$ and
$\ell\ge D_N$, and $d\ge0$. In particular every worst-budget vector
dominates $(1,0,D_N)$ and every weighted supremum is at least the value
in (SRF.17). The one-read static service attains both bounds. $\square$

## 5. Deleting one coupling destroys uniform finite-read recovery

**Proposition 5.1 (deletion sensitivity on the enlarged entire fiber).**
Delete only the positive equality record $(0,LL,1,LR,=)$ in (SRF.14).
Retain the other positive record, the negative record, both literals,
the full old row and all its six inequalities. Every remaining record
keeps both guards; the deleted equality's endpoint-existence conditions
also hold automatically from the old reached holes. The resulting
entire fiber is

$$
\begin{aligned}
 U^- =\{\langle\langle x,b\rangle,
        \langle\rho(t),t\rangle\rangle: &\ b\in\{\alpha,\beta\},\ t\text{ branch},\ x\in\mathcal T,\\
 &\rho^2(x)\ne\rho(t),\quad
 x,b,\rho(t),t\text{ pairwise distinct}\}.
\end{aligned}
\tag{SRF.20}
$$

For every original-prefix depth $h$ this fiber contains two sources
agreeing through $h$ and having different whole $Q$ rows. No permitted
static or serial source-total service on $U^-$ has a uniform finite new-read
budget, at any legal certified entry epoch.

Proof. The literals still give the displayed leaf and branch conditions,
the remaining positive record gives $z=\rho(t)$, and the negative record
is exactly $\rho^2(x)\ne\rho(t)$. The old row gives pairwise distinctness.
All involved old holes are originally reached and remain reached under
$\rho$, so both endpoint guards hold. These facts also prove the reverse
inclusion in (SRF.20), without selecting a subfiber.

For the counterpairs choose $b=\alpha$ and
$t=t_0=\langle\alpha,\alpha\rangle$. Given $h$, set $k=\max(3,h)$.
Let $a$ be the complete binary tree of depth $k$ with all leaves $\alpha$,
and $a'$ the same tree with one depth-$k$ leaf changed to $\beta$.
Take $x=\langle a,a\rangle$ and $x'=\langle a,a'\rangle$. These trees
have depth $k+1>1$, while $t_0,\rho(t_0)$ are distinct depth-one trees
and $b$ is a leaf; all six old inequalities hold separately for each
source. The action preserves original branches, so $\rho^2(x)$ and
$\rho^2(x')$ have depth at least $k+1>1$ and cannot equal $\rho(t_0)$.
Thus both sources belong to the entire $U^-$ with every retained record.

The only changed leaf is at original depth $k+3>h$, so their original
prefixes agree through $h$. Both target rows have all four cuts reached
and the same outside
$\langle\langle\langle\square_1,\square_2\rangle,\alpha\rangle,
\langle\square_3,\square_4\rangle\rangle$.
The first two target values are $a,a$ in one and $a,a'$ in the other.
Their depths exceed those of $\rho(t_0),t_0$, so the complete partitions
are respectively $\{\{1,2\},\{3\},\{4\}\}$ and the discrete partition.
They are different whole rows.

As $h$ is arbitrary, every determining original prefix is refuted. The
operational implication (ARH.2.3), whose locality and finite reply-tree
proof applies independently of presentation syntax, excludes every
uniform finite-read serial competitor. This is a universal consequence
for the enlarged fiber, witnessed by actual pairs for each requested
depth, not a finite-sample inference or an undecidability assertion.
$\square$

## 6. Suppliers and boundaries

**References 6.1 (bounded source and literature comparison).**

| Source | Exact reused interface and limit |
| --- | --- |
| [ARH, §§1–3, 10–18][ARH] | Actual acquired whole fiber and access cut; common original-depth charts and source bijection; exact aligned constraint automata; within-chart Bad; determining-prefix decision and witnesses. Its §16.1 supplies the entire consumer fiber, rows and one-read count. Lemmas 1.3–1.4 prove the additional common physical-action interpretation; Proposition 1.5 provides cross-chart terminal labels. |
| [ABC, Proposition 6.4 and §8.1][ABC] | Same-source nonexpansive cap at $M=\max(N,5)$, cleanup and the stated cofinal parameters. §8.1 specifies the address-before-source quantifier obligation; it does not already decide it for $\mathfrak S$. |
| [JRF, §§4–7][JRF] | Finite control, finite-length optimization, cofinal/Pareto reasoning and rational same-run minimization, including zero weights. Its literal-only source formulas are replaced by the proved §1 interface, not presumed valid on coupled inputs. |
| [SCR, §§9–10][SCR] | Epoch-four raw normalization has an additive address bound; no cap-four joint dominance or optimization is claimed here. |
| [SLH, §§2, 59–62, 69, 74][SLH] | Paid original acquisition, old-row correspondence, aligned suffix coordinates, static decoder and physical locality. Shared suffix coordinates are an existing method; the all-chart action factorization and full-row terminal correspondence here are the added deductions. |
| [AOF, Assumption 1.1 and §§3–5][AOF] | Exact resources on the actually acquired root-to-proper-descendant certificate family, not on arbitrary $\mathfrak S$ inputs. |
| [TPO, Definition 1.2, Corollary 4.2 and Proposition 5.2][TPO] | At the pinned snapshot, the ambient Kuncak–Rinard term-power language cannot uniformly define the all-shape native normal domain. That specific obstruction preserves ARH's $\mathfrak S$ and constructor-elimination decisions and the existing resource suppliers. No normal-domain Assumption 7.3 enters this volume. |
| [Nils Klarlund and Anders Møller, *MONA Version 1.4 User Manual*, January 2001, §§7.1–7.2, printed pp. 39–40][MONA] | Primary `literature-attested` supplier: first-order positions in the infinite binary successor tree, finite-set variables, fixed successor compositions, and WS2S decision by finite bottom-up tree automata, with counterexamples. Page 39 explicitly states that ordinary bottom-up tree automata suffice for validity and counterexamples; page 40 defines their finite transitions via the one-state-space guided special case. It supplies logic decision only after the explicit formulas and run encoding of Lemma 1.4. |

The new `repo-derived` mathematical increment is the all-$\mathfrak S$
common-word/source correspondence, its exact cross-chart whole-row
terminal language and the sharp full-fiber address/price consumer.
The Pareto and weighted procedures use the stated existing finite
optimization suppliers after that bridge. The MONA citation concerns its
ordinary WS2S semantics; no restrictions with a third “don't-care” value
are used. No MONA run, solver implementation, complexity bound or
unrestricted logical interpretation is asserted.

The TPO exclusion is for its exact four-sort covariant $\{F\}$-term-power
of relational Presburger arithmetic: terms, shapes, shape-tagged leafsets
and partial Boolean values, with same-shape pointwise inner formulas,
guarded selectors and fixed-numeral leafset cardinality predicates.
Its outer language has no quantifier over leaf addresses or operation
selecting a rank at a variable leaf. The nondefinability permits any fixed
finite parameter tuple, but not parameters depending on the varying input.
This is the source language of TPO Definition 1.2 and Corollary 4.2;
it is not the binary-position and finite-set language used in Lemma 1.4.

Counterexample 1.6 rules out one direct same-root physical-word encoding;
it does not refute the $\mathfrak S$ synthesis theorem or prove failure
of the larger constructor-elimination family $\mathcal E_{\rm CE}$.
The latter family is outside this volume's synthesis conclusion. Its
eliminated parameters need not satisfy the common original-frontier
routing proof without further work. Arbitrary variable left-prefix
deletion, shifted subtree equality and arbitrary constructor-context
closure are not supplied by the cited automata decision theorem.

The synthesized finite table is a mathematical effective service under
the original paid operation contract. It neither refunds acquisition and
installation nor bounds local work, uniform storage, physical time or
energy. Pointwise static traversal in a negative case need not have a
uniform finite resource bound. No assertion about empirical ML training,
generalization, global originality, kernel verification, independent
review or publication follows from these results. Finite exact controls
can test displayed identities and boundary instances; the universal
conclusions rest on the proofs and their named hypotheses.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[SCR]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[TPO]: https://github.com/the-omega-institute/trureturing/blob/28cc5e33857d4969363b213e6f8c4269fd012972/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[MONA]: https://www.brics.dk/mona/mona14.pdf

## 追加锚（本行以下为增补区）
