# Acquired orbit relations and the exact complete-row resource frontier

## 1. The acquired source and the three prices

**Assumption 1.1 (one original source and a complete entry).** Use the finite
free ordered trees and actual substitution of [ARH, Definitions 1.1–1.2][ARH]:

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
$$

The reply alphabet is $\mathcal A=\{\alpha,\beta,\mathsf b,\bot\}$,
where $\mathsf b$ denotes a branch and $\bot$ an absent address. For arbitrary
finite prefix-free original cuts $P,Q$, the entire row $R_P(u)$ consists of
the concrete exterior, the reached holes in address order, and the partition
by equality of their whole original subtrees. Empty cuts, absent cuts and
the root cut are allowed. Fix an acquired old row $R$, a finite literal
history $H_0$, and a finite signed history $H_{\rm rel}$. A record
$(a,s,b,t,\bowtie)$ requires both endpoints to exist and compares the whole
trees $(\rho^a u)|_s$ and $(\rho^b u)|_t$ using $\bowtie\in\{=,\ne\}$.
Either sign is false when either endpoint is absent. The original domain is
exactly

$$
U=\{u:R_P(u)=R,\ r_{\rho^a u}(s)=c\ ((a,s,c)\in H_0),\
                 \operatorname{Rel}_e(u)\ (e\in H_{\rm rel})\}.
\tag{AOF.1}
$$

In particular, all repeated old classes and all original cross-class
inequalities remain constraints, including classes outside the new task.
There is a recognized positive root certificate
$(n,\varepsilon,m,p,=)$ with $p\ne\varepsilon$, allowing exchange of the
two endpoints. The other records are arbitrary within this finite contract.

The acquisition and complete-state conditions are exactly [ARH,
Assumption 1.3 and Proposition 2.1][ARH]. The same original-root register
has actually reached certified epoch $N$ at least every recorded epoch.
Its accessible initial state is common precisely on (AOF.1). No forgotten
size, description, timing field, traversal length or control distinction
is available. In a legal acquired entry $U\ne\varnothing$. Logical empty
inputs will also be recognized below.

A comparator is a deterministic effective program, correct and terminating
on each source in $U$, with arbitrary-address literal $\mathsf{Read}$,
forward actual $\mathsf{ApplyRho}$, and absorbing $\mathsf{Halt}$. Addresses,
updates, local computation and stopping can depend on received replies;
there is no initial uniform action or work bound. There is no reset, moved
root, cloning, unknown-tree equality, identity or witness port. The output
is the entire original $R_Q(u)$. These are the operation and cost contracts
of [JRF, Definitions 1.2–1.3][JRF], with (AOF.1) as the domain.

**Definition 1.2 (upper budgets and same-run prices).** For a comparator $A$
write

$$
\begin{aligned}
c_A(u)&=(q_A(u),d_A(u),\ell_A(u)),&
\ell_A(u)&=\sum_{\text{actual new reads at }s}|s|,\\
b(A)&=(\sup_U q_A,\sup_U d_A,\sup_U\ell_A),&
\mathcal F&=\{v\in\mathbb N^3:\exists A, b(A)\le v\},\\
W_\lambda(A)&=\sup_{u\in U}
 (\lambda_q q_A(u)+\lambda_d d_A(u)+\lambda_\ell\ell_A(u)),&
W_\lambda^*&=\inf_A W_\lambda(A),
\end{aligned}
\tag{AOF.2}
$$

where $\lambda\in\mathbb Q_{\ge0}^3$. Every raw call, including a repetition
or a root call, contributes one to $q$; a root address contributes zero to
$\ell$. The sum precedes the supremum. No product $0\cdot\infty$ occurs
inside a run. Acquisition, certification, installation, address generation,
local work, memory, clocks, retained receipts, output and physical energy
or time are separately supplied and charged; (AOF.2) neither optimizes
these quantities nor makes them free.

## 2. Exact original-source and complete-row coordinates

**Definition 2.1 (supplied orbit coordinates).** Put

$$
T_0=\alpha,\quad T_1=\beta,\quad T_{j+2}=\langle T_{j+1},T_j\rangle,
\qquad w(s)=\#_L(s)+2\#_R(s).
$$

Use [ARH, Theorems 4.2 and 5.2][ARH] with all of (AOF.1), not just the
designated certificate. An incompatible certificate has empty fiber.
Otherwise $m=n+w(p)$, and the exact computed result is

$$
U=\{T_k:k\in S\},\qquad
S=S_0\cup\bigl(\{k\ge B\}\text{ if }\tau=1\bigr),
\quad S_0\subseteq\{e,\ldots,B-1\},
\tag{AOF.3}
$$

where $e=1$ if $n=0$ and $p$ ends in $L$, and $e=0$ otherwise.
Here $B\ge e$ and $\tau\in\{0,1\}$ are effective. This is the supplied
finite/cofinite representation; no assertion that $S$ is an interval is
needed. The $T_k$ are pairwise distinct and $\rho^aT_k=T_{k+a}$.

For clarity, the supplied compiler checks the following entire predicates.
For a nonroot endpoint $(a,s)$, reach is exactly
$k+a\ge w(s^-)+2$; root reach is automatic. Once both endpoints are
reached, their equality is exactly $a-w(s)=b-w(t)$, and their disequality
is the opposite comparison. A literal is eventually branch, with sufficient
threshold $k\ge\max(0,w(s)+2-a)$. For complete $P$, above

$$
B_P=\max\bigl(\{0\}\cup\{w(p^-)+2:p\in P,\ p\ne\varepsilon\}\bigr)
\tag{AOF.4}
$$

its row is the entire cut trie with holes at $P$ and partition by equal
weights. It is compared with every component of $R$. For incomplete $P$,
choose $r$ incomparable with every cut; at
$k\ge w(r)+\operatorname{ht}(C)+2$ the surviving concrete subtree at $r$
has height exceeding the old exterior $C$, so that old row is false.
Below a common threshold, every complete old row, literal and guarded sign
is evaluated exactly on its known finite candidate $T_k$. Repeated
conditions are retained. These are the interfaces of ARH §5.

**Definition 2.2 (whole-domain target coordinates and supplied correspondence).** The map $k\mapsto T_k$
is a bijection from (AOF.3) onto (AOF.1), and the target in these coordinates
is exactly $f(k)=R_Q(T_k)$, including its exterior and full partition.
The finite-output cases are precisely $\tau=0$ or complete $Q$.
For nonempty inputs in those cases there is an effective finite nonempty $F\subseteq S$ and
surjection $\pi:S\to F$, identical on $F$, such that

$$
f=f|_F\circ\pi.
\tag{AOF.5}
$$

For finite nonempty $S$, take $F=S$ and $\pi$ the identity. For $\tau=1$
and complete $Q$, put $D=\max(B,B_Q)$, with $B_Q$ defined by (AOF.4), and take

$$
F=(S\cap[0,D))\cup\{D\},\qquad \pi(k)=\min(k,D).
\tag{AOF.6}
$$

No source restriction to $F$ is made.

The correspondence follows from the cited ARH results as follows. The
root-certificate theorem first excludes every non-orbit source.
The compiler then tests the full conjunction on each small index and proves
its constant truth on every index in the tail. Thus a source in (AOF.1)
has exactly one admitted index, and every admitted index satisfies the
entire old row and every retained record. This proves both domain
inclusions; checking separate existential realizations of records would
not suffice. Computing $R_Q$ on that same tree proves both directions
of the target correspondence.

For complete $Q$ and $k\ge B_Q$, all original cuts are reached. Its exterior
is exactly the cut trie, and its hole values are $T_{k-w(q)}$. Hence the
whole partition, including repeats between different branches, is
$q\sim q'\Longleftrightarrow w(q)=w(q')$. This proves (AOF.5)–(AOF.6).
All smaller indices use direct finite-tree rows; in particular an absent
cut creates no hole. A root cut gives the same single-hole row for all
indices. An empty cut gives the whole concrete tree, not an empty answer.

If $\tau=1$ and $Q$ is incomplete, take $r$ incomparable with its cuts.
For all sufficiently large admitted indices the distinct entire trees
$T_{k-w(r)}$ survive at that fixed position in the concrete exterior.
There are infinitely many target rows. This is also the necessity
argument of [ARH, Theorem 6.1][ARH]. Finite $S$ has finite image regardless
of the shape of $Q$. The compiler detects empty $S$ separately. $\square$

## 3. Entry-static normalization of every serial comparator

**Theorem 3.1 (same-source zero-update simulation).** At every legal entry
of Assumption 1.1, $N\ge1$. For every original comparator $A$ there is an
effective entry-static comparator $A^\circ$ satisfying, for every same
actual source $u\in U$,

$$
\operatorname{out}_{A^\circ}(u)=\operatorname{out}_A(u),\qquad
q_{A^\circ}(u)=q_A(u),\qquad d_{A^\circ}(u)=0,\qquad
\ell_{A^\circ}(u)\le\ell_A(u).
\tag{AOF.7}
$$

It terminates on each such source, without a common bound on the original
schedules, physical addresses or local work. Equality of physical
histories or of nonpriced resources is not asserted.

Proof. Nonemptiness and the recognized certificate give
$m=n+w(p)\ge1$, and actual certification gives $N\ge m$. This derives
the entry bound from acquisition, rather than imposing a new assumption.
Write $x=N+k\ge1$. The guarded orbit formula supplied by [ARH §4][ARH]
and [SLH §6][SLH] is

$$
\begin{array}{c|cccc}
\text{address type}&\bot&\alpha&\beta&\mathsf b\\
\hline
s\text{ ends in }R, v=w(s)&x<v&x=v&x=v+1&x\ge v+2\\
s\text{ ends in }L, v=w(s)&x\le v&\text{never}&x=v+1&x\ge v+2.
\end{array}
\tag{AOF.8}
$$

The root replies $\alpha,\beta,\mathsf b$ at indices $0,1,\ge2$.
For $v\ge2$ choose the actual word

$$
z(v)=\begin{cases}R^{v/2},&v\text{ even},\\
 LR^{(v-1)/2},&v\text{ odd}.
\end{cases}
\qquad |z(v)|=\lceil v/2\rceil.
\tag{AOF.9}
$$

It ends in $R$ and has weight $v$. The lower bound on its length follows
because each letter has weight at most two; this shortest-word fact is
also [JRF, Definition 2.1][JRF].

Suppose the simulated comparator has made $t$ updates and requests a
nonempty physical word $s$. Put $v=w(s)-t$. The desired reply is the row
of (AOF.8) with this $v$ and entry variable $x$. The following actual
entry query and local decoding provide it on every $x\ge1$:

| Effective weight | Actual entry address | Decoding |
| --- | --- | --- |
| $v<0$ | $\varepsilon$ | constant $\mathsf b$ |
| $v=0$ | $\varepsilon$ | identity on the reachable $\beta,\mathsf b$ |
| $v=1$, original last edge $R$ | $L$ | $\bot\mapsto\alpha$, $\beta\mapsto\beta$, $\mathsf b\mapsto\mathsf b$ |
| $v=1$, original last edge $L$ | $L$ | identity |
| $v\ge2$, original last edge $R$ | $z(v)$ | identity |
| $v\ge2$, original last edge $L$ | $z(v)$ | merge $\alpha$ into $\bot$, keep the other replies |

Unreachable decoder inputs may be assigned arbitrarily. For an original
root request, use the actual root: decode identically if $t=0$, and to
the constant branch if $t\ge1$. The table follows directly from (AOF.8).
Every new address has length at most $|s|$: in the last two cases
$\lceil v/2\rceil\le\lceil w(s)/2\rceil\le|s|$, and the exceptional
addresses have length zero or one. The root case has length zero.

Simulate $A$'s complete control locally, retaining its simulated epoch.
A simulated update changes only that local state. For each simulated
read, perform exactly one actual read in the table, record the actual
receipt, and supply the decoded value to simulated control. Induction
on the original finite run on each $T_k$ proves identical successive
simulated replies, choices and final output. Each transformation and
simulation step is finite, so pointwise termination transfers. This
argument permits unbounded reply-dependent update sequences across sources
and different stopping depths. Halt has no outgoing action. Counting the
actual calls and summing their actual lengths proves (AOF.7).

The decoded values and simulated epochs are local mathematical data.
Only the actual entry-epoch reads are new physical receipts. In particular,
the $v=1$ decoding is not an acquired alpha reply at the submitted $L$.
All incoming receipts keep their original meanings. $\square$

## 4. Completeness on the infinite fiber before finite optimization

**Theorem 4.1 (finite actions and representatives are operationally complete).**
In the nonempty finite-output cases of Definition 2.2, let $M=\max F$ and put

$$
\mathcal M=\{\varepsilon,L\}\cup\{z(v):2\le v\le N+M\}.
\tag{AOF.10}
$$

Consider finite decision trees on $F$ using these actual entry addresses.
A node can halt exactly when its surviving indices have a common full row;
otherwise a read must split them into at least two nonempty reply classes.
Unreachable children need no continuation. Every path has at most
$|F|-1$ reads. Each such tree extends effectively to a source-total actual
service on the entire $U$, with exactly its representative run's costs:

$$
c_B(T_k)=c_B(T_{\pi(k)})\qquad(k\in S).
\tag{AOF.11}
$$

Conversely every original source-total comparator $A$, even with no
uniform cost bound, admits such a tree and extension $B$ for which

$$
\begin{aligned}
c_B(T_j)&\le c_A(T_j)&& (j\in F),\\
b(B)&\le b(A),\qquad
W_\lambda(B)\le W_\lambda(A)&& (\lambda\in\mathbb Q_{\ge0}^3).
\end{aligned}
\tag{AOF.12}
$$

The last two inequalities compare worst budgets and same-run suprema;
no same-source inequality between $B$ and $A$ is asserted for $k\notin F$.

Proof. First restrict the entry-static simulation of Theorem 3.1 to the
finitely many actual sources $T_j$, $j\in F$. Every one of those runs is
finite by source-totality. They can be computed on the known candidate
trees and their finite union unfolded into one finite reachable reply
tree. The common control at a common transcript fixes the next action;
source-dependent local work supplies no extra branch. No uniform bound
on $A$ was assumed, and no search for a bound is used in this construction.

A static nonroot request ending in $R$ of weight $v\ge2$ can be replaced
by $z(v)$ with identical replies and no longer address. A request ending
in $L$ of weight $v\ge2$ is decoded from $z(v)$ by merging alpha into
absence, again with no greater length. Weight one is $L$; root is retained.
If $v>N+M$, every representative reply is absent, for either last edge,
and that request is simulated without a source call. Remove every query
whose reply is already constant on its surviving representative set.
Decoding a refined reply can be represented by equal child continuations.
Stop immediately whenever the required entire row is already common.
Each retained read now splits its finite surviving set, so its depth is
at most $|F|-1$. These operations do not increase any representative's
cost. The addresses remaining are precisely in (AOF.10).

It remains to prove that this finite tree is implementable on all original
sources, rather than only on the representatives. For finite $S$ this is
immediate. In the tail case $M=D$, and for every $a\in\mathcal M$ there is
a computable reply map $\delta_a$ with

$$
r_{T_{N+\pi(k)}}(a)=\delta_a(r_{T_{N+k}}(a))\qquad(k\in S).
\tag{AOF.13}
$$

The map is identity on replies realized below $D$; replies realized only
in the tail map to the reply at $D$. This is well-defined. For $z(v)$,
$v\le N+D$: if $N+D\ge v+2$, the entire tail is branch; if $N+D=v+1$,
only beta and branch are merged; if $N+D=v$, only alpha, beta and branch
are merged. In the latter two cases the merged extra replies occur on no
index below $D$. At root, only $N+D=1$ is exceptional, when $N=1,D=0$
and all allowed indices are tail. For $L$, use its threshold $x=2$:
if $N+D\ge3$ the tail is branch; if $N+D=2$ merge beta and branch;
if $N+D=1$ all allowed indices are again tail. Thus the endpoint and small
index exceptions are included. This proves (AOF.13) on the whole $S$.

Run the finite tree using actual reads at its listed addresses, feeding
$\delta_a$ of each actual reply into its representative control. Induction
on this finite execution keeps $\pi(k)$ among the surviving indices.
The halt output is $f(\pi(k))=f(k)$ by (AOF.5), so it is the entire correct
original row. Every actual source follows exactly its representative's
addresses and halting depth, proving (AOF.11) and termination. This changes
neither the physical source nor its root; $\pi$ is a proof and decoding
map, not a supplied source identity or a reset. Receipts record the raw
replies before $\delta_a$.

Since every representative is itself an allowed actual source and
$\pi$ is onto, the maximum of each cost, or each weighted path sum, in
the extension is its maximum over $F$. Combine this equality with the
representative inequalities proved above and then take the supremum over
all of $S$ to obtain (AOF.12). This proves the two operational directions
before imposing the finite strategy domain.

Every nonempty node of the finite tree has an actual witness $T_j$ with
$j$ in its surviving set. An extension's additional raw reply branches
need not have a witness in $F$: their exact source set is obtained by
intersecting (AOF.3) with the finitely many raw reply inequalities (AOF.8)
along that branch, and the stipulated decoder choices. This is an effective
finite/cofinite set; if nonempty its least index gives an actual witness.
Thus unreachable branches are never charged or used as lower-bound
witnesses, while every attained maximum has a concrete allowed witness.
$\square$

## 5. Exact joint budgets and all rational same-run prices

**Theorem 5.1 (attained operational optimum).** For every input of
Assumption 1.1 one can compute the full feasible upper-budget region and
its Pareto basis, and separately every $W_\lambda^*$. In the nonempty
finite-output cases the basis is finite, nonempty, and consists of
attained triples $(q,0,\ell)$. Every rational nonnegative weighted minimum
is finite and attained by an actual entry-static service. In the infinite-
output case the finite upper-budget region is empty, and

$$
W_\lambda^*=\begin{cases}
\infty,&\lambda_q>0\text{ or }\lambda_\ell>0,\\
0,&\lambda_q=\lambda_\ell=0.
\end{cases}
\tag{AOF.14}
$$

A correct source-total service attains the stated extended value in either
case. An empty logical input is detected; with the convention that empty
suprema of nonnegative costs are zero, its basis is $\{(0,0,0)\}$ and all
its prices are zero. It represents no nonempty acquired entry.

Proof. In the finite-output case Theorem 4.1 supplies a finite address set
and a proved finite depth bound against *every* original comparator.
Therefore enumerate the finite trees specified there, compute their full
row labels and their actual representative path costs, and extend their
services by (AOF.13). Each tree is feasible on the entire original domain.
Conversely (AOF.12) puts a member of this finite collection below any
original comparator in all worst coordinates and in every weighted
worst-run objective. Thus minimizing this collection is exact for the
whole comparator class, even when a proposed competitor has unbounded
costs across sources.

Here is an explicit finite recursive formulation, using only ordinary
finite decision-tree minimization as in [JRF §§6–7][JRF]. For nonempty
$E\subseteq F$, let $E_{a,c}=\{j\in E:r_{T_{N+j}}(a)=c\}$. If $f$ is
constant on $E$, set $\mathcal P(E)=\{(0,0)\}$ and $V_\lambda(E)=0$.
Otherwise use the addresses splitting $E$ and only their nonempty children:

$$
\begin{aligned}
\mathcal P(E)
 &=\operatorname{Min}\bigcup_{a\text{ splits }E}
 \left\{\left(1+\max_c q_c,\ |a|+\max_c l_c\right):
           (q_c,l_c)\in\mathcal P(E_{a,c})\right\},\\
V_\lambda(E)
 &=\min_{a\text{ splits }E}
 \left(\lambda_q+\lambda_\ell|a|+\max_c V_\lambda(E_{a,c})\right).
\end{aligned}
\tag{AOF.15}
$$

Each child is a strict subset, so both recurrences terminate. A splitting
address exists whenever two surviving indices have different rows: the
root distinguishes $N+j=1$ from larger indices, $L$ distinguishes index
two from larger indices, and $z(N+j)$ for $N+j\ge2$ singles out that
index by its alpha reply. These addresses are in (AOF.10).

Induction proves the recurrences by choosing the first actual read and
independent continuations on its mutually exclusive reply branches.
Coordinatewise maxima in the first recurrence are simultaneous upper
budgets, not sums of separately realizable benefits. The second recurrence
adds the current cost to the maximum *continuation sum on one branch*.
It does not scalarize $\mathcal P(E)$. Dominated child vectors can be
removed in the first recurrence by monotonicity. In both recurrences a
homogeneous node halts, including early halts before any read. Zero weights
cause no difficulty because the proved finite collection is already
cofinal for every comparator, independently of any positive weight.

The basis is $\{(q,0,l):(q,l)\in\mathcal P(F)\}$; its upward closure is
exactly $\mathcal F$. A minimal feasible upper budget is the exact worst
vector of its witness: any strict slack would give a smaller feasible
budget. The scalar value is $V_\lambda(F)$, with an attaining tree selected
by the second recurrence. Maxima have source witnesses in $F$, since all
those indices are actual sources. Distinct coordinate maxima need not be
witnessed by one source. The scalar maximum does have a single-run witness.

If the target image is infinite, a uniformly bounded $q$ would give a
finite four-reply tree and hence finitely many outputs. Source-totality
ensures that each reachable deterministic segment ends in a read or halt;
no uniform local-work bound is required for this finite-depth argument.
Thus every correct comparator has unbounded $q$. If some comparator had
bounded $\ell$, apply Theorem 3.1 and remove repeated static requests,
simulating them from their already acquired receipts. There is at most
one remaining root request. Every other actual request has length at
least one, giving $q\le\ell+1$ sourcewise, a contradiction. Hence both
worst quantities are infinite for every comparator, proving the first
case of (AOF.14).

For existence without a uniform budget, read successive $R^a$ at entry,
starting at $a=0$, until the first leaf. In $T_{N+k}$ it occurs at
$a=\lfloor(N+k)/2\rfloor$; alpha or beta determines $N+k=2a$ or $2a+1$.
Compute $k$ and the full original row locally. Every actual source is
finite, so this is a terminating static service. It has zero update cost
and proves the second case of (AOF.14), including the all-zero weight
vector. It also witnesses existence in the infinite-price case. This
construction claims no uniform read, length, memory or work bound.
The empty-domain convention is realized by immediate halt. $\square$

## 6. A signed-guard-sensitive family of entire rows

**Theorem 6.1 (one acquired family with scalable complete-row demands).** Take

$$
\begin{gathered}
P=\{L,R\},\quad R=(\langle\square_1,\square_2\rangle,
                    \{\{1\},\{2\}\}),\quad H_0=\varnothing,\quad N=1,\\
H_{\rm rel}=\{(0,\varepsilon,1,L,=),(0,RR,1,R,\ne)\},\\
Q_d=\{LL,LR\}\cup\{R^iL:1\le i<d\}\cup\{R^d\},\qquad d\ge2.
\end{gathered}
\tag{AOF.16}
$$

The entire acquired fiber is $\{T_k:k\ge4\}$. Its $Q_d$ target has exactly
$2d-3$ entire rows, indexed by the individual indices $4,\ldots,2d-1$
and the one tail $k\ge2d$. There are actual services and all-original-
service lower bounds given by the finite recurrences below for every $d$.
The exact raw price is the supplied ordered-search capacity specialization

$$
\min\{h:2d-3\le3\cdot2^h-2\}
 =\left\lceil\log_2\frac{2d-1}{3}\right\rceil.
\tag{AOF.17}
$$

Removing only the negative record gives the entire fiber $k\ge2$, exactly
$2d-1$ rows, and raw price $\lceil\log_2((2d+1)/3)\rceil$.

Proof. The positive certificate selects $k\ge1$ by [ARH, Theorem 4.2][ARH].
The old row selects exactly $k\ge2$: the children are $T_{k-1},T_{k-2}$
and are different. For the negative record, $RR$ is reached originally
exactly when $k\ge4$, whereas the epoch-one $R$ endpoint is reached when
$k\ge1$. Once both exist, their complete values are $T_{k-4},T_{k-1}$,
which are always different. Thus the sign, including its guard, selects
exactly $k\ge4$. An absent endpoint cannot produce this negative record.
The paid producer [ARH, Proposition 2.1][ARH] applies to these fixed
coordinates, so the acquisition has both full-fiber directions and needs
no retained index or description.

The cut $Q_d$ is complete. For $k\ge2d$ all its cuts are reached, its
exterior is its trie, and its partition is by the weights

$$
2,\ 3,\ 3,5,\ldots,2d-1,\ 2d.
\tag{AOF.18}
$$

In particular $LR$ and $RL$ repeat the same class; no other weights repeat.
For $2\le k<2d$, the right spine terminates at $R^{\lfloor k/2\rfloor}$
with the concrete leaf alpha or beta according to the parity of $k$.
That terminal position is not removed by $Q_d$. Its position and label
identify $k$ from the exterior; the reached holes and all their equalities
are still those of the actual tree. These rows are pairwise different
and different from the all-holes tail. This proves the two row counts,
including $d=2$, where the signed family has one constant row.

Write $a=4$ for the signed family and $a=2$ when only the negative record
is removed, and $b=2d$. The target index is $\min(k,b)$ on $k\ge a$.
At epoch one, a threshold $t\ge1$ is the actual read $z(t+1)$ of length

$$
C(t)=\left\lceil\frac{t+1}{2}\right\rceil,
\tag{AOF.19}
$$

whose four replies specify $k<t$, $k=t$, $k=t+1$, $k\ge t+2$.
Every nonempty arbitrary address either has exactly such a partition or,
if it ends in $L$, a coarsening at no smaller minimal length. The root and
$L$ are constant on $k\ge2$. Theorem 3.1 removes all serial updates
without increasing any source's costs. Theorem 4.1 gives the full-tail
extension and worst-cost completeness. Thus no original service is omitted
by optimizing these thresholds.

On an interval $[l,r]\subseteq[a,b]$ of remaining target indices, useful
thresholds reduce to $l-1\le t\le r-1$. Smaller ones are constant.
A threshold $t>r$ is constant on the representatives. The partition at
$t=r$ is refined by $t=r-1$, whose length is no greater, with any unnecessary
extra distinction merged locally. The two potentially nonsingleton children
are $[l,t-1]$ and $[t+2,r]$, intersected with $[l,r]$; the other two children
halt at their individual rows. At the last tail label, all physical replies
corresponding to $k\ge b$ select that same full row. Empty children are
unreachable and singleton children halt without a further action.

The two-singleton/two-interval capacity and its ordered-search construction
are [SLH, Theorem 6.2][SLH]: capacity at depth $h$ is $3\cdot2^h-2$.
Here the required thresholds have $t\ge a-1\ge1$ and are all actual
addresses by (AOF.19), so the supplier's construction applies. Its lower
bound applies because (AOF.8) gives at most two interval reply classes
and two singleton reply classes, also after restriction to any surviving
subset: a depth-$h$ tree has capacity at most twice the depth-$(h-1)$
capacity plus two. All target labels have actual source witnesses. Together with the serial normalization this proves
(AOF.17) against all original services. Capacity and ordered search are
suppliers, not new standalone results. $\square$

**Definition 6.2 (exact family recurrences).** For a singleton or empty
integer interval set $E_h(l,r)=E_\infty(l,r)=V_{x,y}(l,r)=0$. For $l<r$,
set $E_0(l,r)=\infty$ and

$$
\begin{aligned}
E_h(l,r)&=\min_{l-1\le t\le r-1}
 \{C(t)+\max(E_{h-1}(l,t-1),E_{h-1}(t+2,r),0)\},\quad h\ge1,\\
E_\infty(l,r)&=\min_{l-1\le t\le r-1}
 \{C(t)+\max(E_\infty(l,t-1),E_\infty(t+2,r),0)\},\\
V_{x,y}(l,r)&=\min_{l-1\le t\le r-1}
 \{x+yC(t)+\max(V_{x,y}(l,t-1),V_{x,y}(t+2,r),0)\}.
\end{aligned}
\tag{AOF.20}
$$

Here $x,y\in\mathbb Q_{\ge0}$, and intervals outside $[l,r]$ in a child
are understood as empty. Each nonempty child is strictly shorter.
These are the exact minimum worst length with at most $h$ reads, the exact
minimum worst length without a read constraint, and the exact same-run
weighted price, respectively. This interpretation follows by the
first-action induction in Theorem 5.1 and the exhaustive threshold
correspondence in Theorem 6.1. The update weight is immaterial at its attained
minimum zero. For the entire joint basis, retain the nondominated pairs
$(h,E_h(a,b))$ for $0\le h\le b-a$ with finite $E_h$; remove any strict
slack in $h$ by nondominance. This supplies a symbolic complete consumer
for arbitrary $d$, not just a finite menu of examples.

**Proposition 6.3 (the exact twenty-one-row frontier).** For $d=12$ in
(AOF.16), the complete Pareto basis and two same-run prices are

$$
\operatorname{Min}\mathcal F=\{(3,0,29),(4,0,27)\},\qquad
W_{(1,0,1)}^*=31,\qquad W_{(3,0,1)}^*=38.
\tag{AOF.21}
$$

Removing only the negative record gives twenty-three rows and minimum
raw count four instead of three.

Proof. The preceding theorem gives the exact interval $[4,24]$ of target
labels and its physical threshold costs. The following table gives the
first-action values in (AOF.20). Column $L_3$ uses at most two further
reads; column $L$ uses $E_\infty$ on the two children; columns $S_1,S_3$
use $V_{1,1},V_{3,1}$. Thus a row is obtained by adding $C(t)$, or
$x+C(t)$, to the maximum of its two strictly shorter child values and zero.
These equations and the singleton bases specify all entries exactly.

| $t$ | $L_3$ | $L$ | $S_1$ | $S_3$ |
| --- | --- | --- | --- | --- |
| 3 | $\infty$ | 29 | 34 | 43 |
| 4 | $\infty$ | 30 | 35 | 44 |
| 5 | $\infty$ | 30 | 35 | 44 |
| 6 | $\infty$ | 31 | 36 | 45 |
| 7 | $\infty$ | 30 | 34 | 42 |
| 8 | $\infty$ | 31 | 35 | 43 |
| 9 | $\infty$ | 31 | 35 | 43 |
| 10 | $\infty$ | 32 | 36 | 44 |
| 11 | $\infty$ | 32 | 36 | 44 |
| 12 | $\infty$ | 33 | 37 | 45 |
| 13 | 29 | 29 | 32 | 38 |
| 14 | 30 | 30 | 33 | 39 |
| 15 | $\infty$ | 30 | 33 | 39 |
| 16 | $\infty$ | 31 | 34 | 40 |
| 17 | $\infty$ | 31 | 34 | 40 |
| 18 | $\infty$ | 32 | 35 | 41 |
| 19 | $\infty$ | 27 | 31 | 39 |
| 20 | $\infty$ | 30 | 34 | 42 |
| 21 | $\infty$ | 31 | 35 | 45 |
| 22 | $\infty$ | 34 | 39 | 49 |
| 23 | $\infty$ | 35 | 40 | 50 |

The column minima give $E_3(4,24)=29$, $E_\infty(4,24)=27$,
$V_{1,1}(4,24)=31$ and $V_{3,1}(4,24)=38$. Explicit attaining services
also give $E_4(4,24)=27$. To specify them, let $t[A,B]$ mean an actual
threshold-$t$ read with the below-$t$ interval continuing by $A$, the
above-$t+1$ interval continuing by $B$, and the two singleton replies
halting. A $0$ child halts at its sole surviving label, or is unreachable
if its interval is empty. Maintain the current interval to interpret
these leaves, and output its precomputed entire original row. Put

$$
\begin{aligned}
A&=13[\,7[4[0,0],10[0,0]],\ 19[16[0,0],22[0,0]]\,],\\
B&=19[\,13[7[4[0,0],10[0,0]],16[0,0]],\ 22[0,0]\,].
\end{aligned}
\tag{AOF.22}
$$

The first has worst vector $(3,0,29)$: indices $21,22,23$ and the whole
tail traverse thresholds $13,19,22$, of lengths $7,10,12$. The second
has worst vector $(4,0,27)$: indices $9,10,11,12$ traverse $19,13,7,10$,
of lengths $10,7,4,6$. All its other paths have no larger coordinates.
Consequently $B$ has worst same-run sum $31$ for $(q,\ell)$ weights
$(1,1)$, and $A$ has worst sum $38$ for weights $(3,1)$.

The capacity lower bound excludes two reads, since $21>10$. The $L_3$
column excludes length below 29 at three reads; the $L$ column excludes
length below 27 at *any* depth. Hence every finite feasible triple is
above one of the two in (AOF.21). The $S_1,S_3$ columns separately supply
the weighted lower bounds; they do not add separate coordinate suprema.
The operational completeness theorem transfers all these lower bounds
to arbitrary original serial services. Finally $23>3\cdot2^3-2=22$
and $23\le3\cdot2^4-2$, so the unsigned-guard variant needs exactly four
reads. No other record or old class inequality has been removed. $\square$

## 7. Mathematical suppliers and scope

**References 7.1 (bounded source comparison).** The repository interfaces
in this volume are those at source revision
[3f27425f9ac9ce82d412b7f54b3881dc2da20ce3](https://github.com/the-omega-institute/trureturing/tree/3f27425f9ac9ce82d412b7f54b3881dc2da20ce3).

| Supplier | Exact use and boundary |
| --- | --- |
| [ARH §§1–8][ARH] | Complete acquired-state contract; guarded whole-endpoint semantics; positive root classification; exact finite/cofinite indices with every old condition; entire-row finite-budget criterion and sufficient consumers. The classification and compiler are supply. Theorem 8.3 prevents treating an infinite orbit fiber as a finite union of exact literal-only old inputs. |
| [ARH §§10–18 and §§19–25][ARH] | Synchronous and constructor-elimination families give their own full-row decisions and paid consumers. Their retained general joint-minimum questions are not settled here; recognition of the positive root record is essential to the present operational theorem. |
| [JRF §§1–7][JRF] | Sourcewise versus worst-budget order, actual read/update/length accounting, shortest words, finite strategy optimization, and separate same-run weighted minimization are supplied methodology. Its literal-only admissibility and equal-row predicates are not invoked on arbitrary relation histories. |
| [SCR §§9–10][SCR] | Sharp epoch-four general transport and its complete-row consumers apply on their stated all-tree interfaces. They do not supply the acquired-orbit entry-static, nonexpansive joint optimum proved here. |
| [SLH §6.2 and §§59–62][SLH] | The ordered-search capacity $3\cdot2^h-2$ and its construction; complete old-row acquisition, repeats, disequalities and source-continuous handoff. These are attributed supply, not new capacity or generic minimization theorems. |
| H. Comon et al., [*Tree Automata Techniques and Applications*, author version, §1.4, pp. 31–34](https://inria.hal.science/hal-03367725v1/document) | `literature-attested`: the ranked tree homomorphism definition makes this $\rho$ a fixed linear homomorphism; Theorems 1.4.3–1.4.4 give their stated language closures. Those closures do not provide the acquired-state, arbitrary-service or cost correspondences here. |

The source-relative additions are (AOF.7), the full-fiber two-way
operational completeness of Theorem 4.1, the exact optima obtained from
that completeness, and their signed-guard-sensitive complete-row consumer.
They are `repo-derived` ordinary deductions. Finite minimax recursion,
Pareto order, atomic root classification, unification and automata
background remain suppliers; no global novelty or priority follows from
this bounded comparison.

**Assumption 7.2 (retained mathematical boundaries).** The interpretation
is finite free ordered trees with the fixed substitution, complete actual
entry and original physical operations of Assumption 1.1. Unrestricted
coupled histories without the recognized certificate are outside the
optimization theorem. No undecidability or exact literal-history
conversion is inferred; the newer ARH family results retain their own
scope. A task output does not itself erase the incoming relations or the
new actual receipts; any later entry requires its own complete-state and
paid retention contract. No probability-law replacement, physical
acquisition shortcut, training or generalization assertion, or
cross-model cost equivalence is part of these deductions.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[SCR]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md

## 追加锚（本行以下为增补区）

## 8. Stationary interval reading with a zero origin

**Definition 8.1 (unknown age and the two new prices).** Use the native
finite ordered trees and actual constructor port of Assumption 1.1,
and $T_n=\rho^n\alpha$ of Definition 2.1. This section has a separate
entry contract: the source is one unknown $T_n$ with public finite
integer endpoints $0\le L\le n\le U$. The reader initially knows only
those endpoints and common controls. It must output $n$ correctly on
every source in $[L,U]$ using stationary literal $\mathsf{Read}$ alone.
There is no certified current age, acquired distinguishing history,
subtree or epoch oracle, and no source update. Every submitted finite
$L/R$ word costs one chronological call, including repetitions and the
root word $\varepsilon$. A nonempty suffix at a leaf returns $\bot$.

For a deterministic reader $A$ terminating on this entire finite interval,
let $q_A(n)$ be its chronological calls and let $p_A(n)$ be the maximum
submitted relative word length, with value zero for no submissions. Set

$$
K(L,U)=\min_A\max_{L\le n\le U}q_A(n),\qquad
M(L,U)=\min_A\max_{L\le n\le U}p_A(n).
\tag{AOF.23}
$$

These are separate worst-case coordinates on the same source domain.
Their maxima need not occur on the same source. The peak in (AOF.23)
is not the sum $\ell$ in (AOF.2); no expected, randomized, total-length,
workspace or physical-time objective is imposed. Acquisition and local
work are not source queries supplied by this interval contract.

**Definition 8.2 (notation for the supplied actual queries).** Reuse the
guarded navigation (ARH.4.3), the constructor table (AOF.8), shortest
words (AOF.9) and [JRF, Definition 2.1][JRF]. Write $E$ for the root
query, $P_t$ for a nonempty word of weight $t$ ending in $R$, and $S_t$
for a word of weight $t-1$ ending in $L$, where $t\ge2$. Their actual
response functions in the current-age coordinate are

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\
\hline
E&\text{never}&n=0&n=1&n\ge2\\
P_t&n<t&n=t&n=t+1&n\ge t+2\\
S_t&n<t&\text{never}&n=t&n\ge t+1.
\end{array}
\tag{AOF.24}
$$

For a nonempty word $p$, (ARH.4.3) requires
$n\ge w(p^-)+2$, not just $n-w(p)\ge0$. The final edge converts that
guard into the displayed $P$ or $S$ threshold, also at ages zero and
one. Thus every actual word has one of these response functions. The
supplied shortest representatives have length $\lceil t/2\rceil$:
for $s\ge1$, use $R^s,LR^s$ for $P_{2s},P_{2s+1}$ and
$R^{s-1}L,R^{s-1}LL$ for $S_{2s},S_{2s+1}$. Every power denotes the
fully materialized finite word submitted to the port. There is no
$P_1$: an $R$-ending word has weight at least two, while the weight-one
word $L$ realizes $S_2$. This is supplier notation within the new
contract, not a new navigation or shortest-word result.

**Theorem 8.3 (the zero boundary and exact native interval calls).** Put
$N=U-L+1$ and reuse the positive ordered-search capacity of [SLH,
Theorem 6.2][SLH], as applied in (AOF.17)--(AOF.19):

$$
C_k=3\cdot2^k-2\quad(k\ge0),\qquad
A_0=1,\quad A_k=3\cdot2^k-3\quad(k\ge1).
\tag{AOF.25}
$$

Under Definition 8.1, an interval is recoverable in at most $k$ actual
calls exactly when $N\le C_k$ for $L\ge1$, or $N\le A_k$ for $L=0$.
Consequently

$$
K(L,U)=
\begin{cases}
0,&N=1,\\
K_+(N):=\left\lceil\log_2\dfrac{N+2}{3}\right\rceil,
 &N\ge2,\ L\ge1,\\
K_0(N):=\left\lceil\log_2\dfrac{N+3}{3}\right\rceil,
 &N\ge2,\ L=0.
\end{cases}
\tag{AOF.26}
$$

Define $K_+(1)=K_0(1)=0$. There is a finite actual adaptive literal
reader attaining this bound. Every smaller call budget has a failure
witness consisting of two actual ages in the interval with the same
complete reply transcript and different required outputs.

**Proof.** Every actual response cell in (AOF.24), intersected with a
surviving interval, is an interval or singleton. Thus truthful histories
leave intervals or singletons, and zero calls can identify only one
candidate. On a positive interval the supplied two-tail/two-singleton
argument gives $C_0=1$ and $C_k=2C_{k-1}+2$: each of the at most two
nonsingleton tails remains positive and has capacity $C_{k-1}$.
Root and $S$ queries have no larger capacity. To verify the construction
in this unknown-age contract, on $[l,l+C_k-1]$, $l\ge1,k\ge1$, set
$c=C_{k-1}$ and submit the shortest actual $P_{l+c}$ representative.
The threshold $l+c\ge2$ is legal. Its absent and branch tails each
have $c$ ages; its alpha and beta replies identify $l+c,l+c+1$ and
halt. The two tails use the supplied recursive reader with budget
$k-1$. This is the native parameter correspondence to the positive
supplier, with no certified epoch added.

At zero, a nonempty word merges ages zero and one into absence. The
root merges ages two and three into branch. Hence no one-call reader
can distinguish $[0,3]$, while the one paid root call distinguishes
$[0,2]$. Therefore $A_1=3$, and the positive value $C_1=4$ cannot be
used here. For $k\ge2$, a first $P_t$ query leaves one zero-origin
absent tail, at most two singleton replies and one positive branch
tail. Their total capacity is at most $A_{k-1}+2+C_{k-1}$. An $S_t$
query has only one singleton, and the root has two singleton replies
and one positive tail, no more than this bound. Empty, truncated and
constant cells also obey these bounds. Thus

$$
A_k\le A_{k-1}+C_{k-1}+2\quad(k\ge2).
\tag{AOF.27}
$$

For attainment on $[0,A_k-1]$, $k\ge2$, submit the actual shortest
$P_{A_{k-1}}$ word. Its threshold is at least three. Its absent tail
has $A_{k-1}$ ages, its branch tail has $C_{k-1}$ ages, and its two
singleton replies halt. Recurse with the respective zero-origin and
positive readers. At $k=1$ use the root as above; at $k=0$ halt at the
sole candidate. Equality in (AOF.27), starting with $A_1=3$, gives
$A_k=3\cdot2^k-3$. The recurrence starts at $k=2$; applying it at
$k=1$ would incorrectly count four ages.

For any shorter interval, restrict the appropriate full-capacity tree
to the public interval. Delete impossible branches and halt as soon
as its surviving interval is a singleton. All thresholds depend only
on public data and previous actual replies, and every continuing
branch decreases its finite call budget. Thus this is an actual
terminating reader using materialized words, not an age oracle.

For a purported reader on a capacity-exceeding interval, its first
query has a truthful response cell exceeding the capacity appropriate
to the remaining budget. Select such a cell and continue. At a
zero-origin one-call node use the explicit collision zero/one for a
nonempty word or two/three for the root. At budget zero at least two
distinct ages remain. If the reader halts earlier, any two remaining
ages already witness failure. The chosen surviving sets are nested;
choose the two ages at the end. Each of their fixed actual $T_n$
sources produces the entire selected transcript, by deterministic
control and (AOF.24). No source is changed midway through a run. They
require different outputs and cannot both be correct at that leaf.
This supplies the lower bound and failure witnesses. Inverting (AOF.25)
gives (AOF.26). $\square$

## 9. One literal reader attaining both minimum prices

**Theorem 9.1 (bounded-domain simulation of each actual query).** For
$U\ge1$ put $m=\lfloor(U-1)/2\rfloor$. For every finite literal word
$p$ there are a source-independent actual word $q_p$ and a finite
reply map $\phi_p:\mathcal A\to\mathcal A$ such that

$$
|q_p|\le\min(|p|,m),\qquad
r_{T_n}(p)=\phi_p(r_{T_n}(q_p))\quad(0\le n\le U).
\tag{AOF.28}
$$

One paid query at $q_p$ suffices for this simulation; a length-zero
replacement still costs that call. The decoded value is local control
data, not an actual receipt at $p$.

**Proof.** If $U\le2$, choose $q_p=\varepsilon$. Its replies distinguish
every age in $[0,U]$. Map its alpha, beta and branch replies to the
supplied table's value for $p$ at ages zero, one and two respectively;
assign any unreachable input arbitrarily. This proves (AOF.28) with
$m=0$, including $U=1$.

If $U\ge3$, then $m\ge1$ and $U\in\{2m+1,2m+2\}$. First replace
$p$ by the shortest globally reply-equivalent $E,P_t$ or $S_t$
representative of Definition 8.2. This does not increase its length.
If that length is at most $m$, use that word and the identity map.
Otherwise its shortest length $\lceil t/2\rceil$ exceeds $m$, hence
$t\ge2m+1$. Use $q_p=R^m=P_{2m}$. On $[0,U]$ its reply cells are
$[0,2m-1]$, $\{2m\}$, $\{2m+1\}$ and, when present, $\{2m+2\}$.
The old query is constantly absent on the first cell, and every other
cell is a singleton. Substitution in (AOF.24) gives all six maps:

| Original query | $\phi_p(\bot)$ | $\phi_p(\alpha)$ | $\phi_p(\beta)$ | $\phi_p(\mathsf b)$ |
| --- | --- | --- | --- | --- |
| $P_{2m+1}$ | $\bot$ | $\bot$ | $\alpha$ | $\beta$ |
| $P_{2m+2}$ | $\bot$ | $\bot$ | $\bot$ | $\alpha$ |
| $P_t$, $t\ge2m+3$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ |
| $S_{2m+1}$ | $\bot$ | $\bot$ | $\beta$ | $\mathsf b$ |
| $S_{2m+2}$ | $\bot$ | $\bot$ | $\bot$ | $\beta$ |
| $S_t$, $t\ge2m+3$ | $\bot$ | $\bot$ | $\bot$ | $\bot$ |

For $U=2m+1$ the branch column is unreachable. Since a replaced
representative had length greater than $m$, the new length is also
at most the original $|p|$. Normalization must precede this argument:
an arbitrary overlong word can have a short equivalent representative.
The displayed refinement proves (AOF.28) on every declared age. $\square$

**Theorem 9.2 (joint call and peak attainment).** Under Definition 8.1,
singletons have $K(L,L)=M(L,L)=0$. For $L<U$,

$$
M(L,U)=\left\lfloor\frac{U-1}{2}\right\rfloor,
\tag{AOF.29}
$$

and one finite reader simultaneously attains (AOF.26) and (AOF.29).
For a nonsingleton interval, call budget $k$ and peak budget $d$ are
jointly feasible precisely when $U\le2d+2$ and the appropriate
capacity inequality of Theorem 8.3 holds.

**Proof.** By the supplied guarded table, any word of length at most
$d$ gives branch on every age $n\ge2d+2$: its weight is at most $2d$,
and its last-edge guard and branch threshold have already been crossed.
The root has the same property, including $d=0$. If
$d<\lfloor(U-1)/2\rfloor$, both $U-1$ and $U$ lie in this common
branch tail. Deterministic adaptive queries of length at most $d$
therefore choose the same subsequent words and receive identical
histories on these two fixed sources, however many calls are allowed.
They cannot output both ages correctly. This proves the peak lower bound.

Apply Theorem 9.1 at every node of the actual call-optimal finite tree
of Theorem 8.3. For each old query, submit the replacement literal
word once and feed its mapped reply into the old control. Induction
on a run on each fixed $T_n$ proves the same simulated replies,
choices and final output; neither the source nor its age changes.
Calls do not increase, and every submitted word has length at most
$m=\lfloor(U-1)/2\rfloor$. The independent call and peak lower bounds
force this one reader's two worst coordinates to be exactly $K$ and
$M$. For $U\le2$ a nonsingleton is separated by one paid root call
with peak zero. A singleton outputs its public age without a query.
The joint-budget characterization follows from the two lower bounds
and their common attaining reader, since $M\le d$ is equivalent to
$U\le2d+2$.

In particular, $[0,3]$ needs two calls while $[1,4]$ needs one.
On $[2,5]$, the mixed literal word $LR=P_3$ gives the four different
replies in one call. A pure-right one-call reader cannot do so: the
root is constant, $R$ merges four/five, $RR$ merges two/three, and
$R^s$ for $s\ge3$ is constantly absent. Two pure-right calls suffice
by $R$ and then $RR$ on branch. Thus the allowed mixed query is a
real resource distinction. $\square$

**Theorem 9.3 (finite-domain and literal-length boundaries).** The
simulation (AOF.28) need not preserve replies beyond its declared
upper endpoint. Positive intervals of any fixed size $N\ge2$ retain
the same optimal call price under translation while their necessary
peak length is unbounded. Embedding the interval reader at a reached
fixed slot prefix $w_0$ of length $D$ gives an upper bound $D+M(L,U)$
for a nonsingleton, with the same $K(L,U)$ calls; a singleton submits
no word. This embedding alone gives no whole-tree-reader lower bound.

**Proof.** With $m=1,U=4$, the map for $P_3$ reads $R$ and decodes
its branch as beta. At age five, $LR=P_3$ actually returns branch
but that map still gives beta. The endpoint restriction is therefore
essential. For translated positive intervals (AOF.26) depends only on
$N$, whereas (AOF.29) diverges with $U$. Every actual submitted word
$w_0p$ has length $D+|p|$ and at a reached slot returns its actual
relative reply. This proves the embedding upper bound. Other whole-tree
addresses could carry information; their exclusion needs a separate
consumer correspondence. A product $K(D+M)$ would merely upper-bound
summed submitted lengths, not optimize that sum. $\square$

**Mathematical citation 9.4 (suppliers and bounded comparison).**
The navigation, shortest words and positive capacity are the suppliers
specified in Definition 8.2 and Theorem 8.3. In particular [SLH,
Definition 6.1 and Theorem 6.2][SLH] concern arbitrary original trees
with certified $M\ge4$; (AOF.19) likewise uses its own epoch-one
coordinate. Those epoch inputs do not supply a physical $P_1$ or an
unknown-age oracle in Definition 8.1. The zero-origin correction,
bounded-query simulation and joint peak result are `repo-derived`
ordinary deductions; the earlier summed-length and general finite
optimization results retain their stated contracts.

Compare R. D. Nowak, *The Geometry of Generalized Binary Search*,
[arXiv:0910.4397v5, §§II-A and V-A](https://arxiv.org/html/0910.4397v5).
Its response-cell formulation and its disjoint-interval example distinguish
point queries from added dyadic-subinterval tests. That comparison supports
using the actual permitted query language here; its binary GBS bounds
provide neither (AOF.25)'s zero correction nor (AOF.29)'s literal peak.
This bounded comparison makes no worldwide novelty or priority claim.

## 追加锚（本行以下为增补区）

## 10. Minimum internal Moore states with common call and peak attainment

**Definition 10.1 (one stationary finite table for a declared interval).**
Keep exactly Definition 8.1: public integers $0\le L\le U$, one unknown
stationary actual $T_n$ with $n\in[L,U]$, literal four-valued
$\mathsf{Read}$ alone, and required complete numeric answer $n$.
A finite Moore controller has a disjoint state set $\mathcal K=Q\sqcup H$,
one common initial state $s_0\in\mathcal K$, and fixed tables

$$
\begin{aligned}
\operatorname{addr}&:Q\longrightarrow\{L,R\}^*,\\
\operatorname{next}&:Q\times\mathcal A\longrightarrow\mathcal K,
&\mathcal A&=\{\alpha,\beta,\mathsf b,\bot\},\\
\operatorname{out}&:H\longrightarrow\mathbb N.
\end{aligned}
\tag{AOF.30}
$$

At a running state $s$ it submits the one fixed fully materialized word
$\operatorname{addr}(s)$, receives its actual reply $a$, and changes to
$\operatorname{next}(s,a)$. The transition table is total on all four
replies. A halt returns its fixed complete integer $\operatorname{out}(s)$,
without another source call. Every installed state counts, including
unused states, redundant halts and unreachable transition destinations.
The current state is the entire changing accessible configuration.
There is no separate address, reply, age, phase, interval, clock, counter,
history or payload register and no source-dependent output decoder.
In particular two different answers require two different halting states.

The same table and initial state serve every age in this one interval.
Literal addresses, transitions and outputs may depend on the declared
endpoints. Their representation, static storage, installation, address
transmission and complete output production have separate costs. This
contract counts abstract states, chronological calls and peak submitted
literal length, rather than total physical memory or elapsed time.
Write $J_{\min}(L,U)$ and $S_{\min}(L,U)$ for the minimum running and
total state counts among controllers terminating correctly throughout
the interval. The call and peak coordinates keep (AOF.23)'s conventions,
including one paid empty-word call and zero peak for no submissions.

**Theorem 10.2 (exact state minima and one common native witness).** Put
$N=U-L+1$ and

$$
J(L,U)=
\begin{cases}
0,&N=1,\\
\left\lceil\dfrac{N-1}{3}\right\rceil,&N\ge2,\ L\ge1,\\
\left\lceil\dfrac N3\right\rceil,&N\ge2,\ L=0.
\end{cases}
\tag{AOF.31}
$$

Under Definition 10.1,

$$
J_{\min}(L,U)=J(L,U),\qquad S_{\min}(L,U)=N+J(L,U).
\tag{AOF.32}
$$

One actual controller has exactly $J(L,U)$ running states and $N$ halts
and simultaneously attains the supplied $K(L,U)$ and $M(L,U)$ of
Theorems 8.3 and 9.2. All its states are reached on admitted sources.
The separate worst call and peak values need not occur on the same age.

**Proof.** First obtain the state lower bound on general shared graphs.
For $N\ge2$ the common initial state cannot halt. Take the directed
union of the $N$ actual finite runs, with $j$ running vertices and
exactly $N$ terminal vertices. There are exactly $N$ because the runs
are deterministic, their required integers differ, and each run ends
at one fixed-output halt. Every vertex is reachable from the common
initial vertex. Select one incoming edge along a shortest root path
for each noninitial vertex. These distinct edges give

$$
j+N-1\le e\le4j,
\tag{AOF.33}
$$

where $e$ counts distinct directed successor edges used by actual runs.
The upper bound uses at most four actual replies per running state;
two replies going to one successor can only decrease this edge count.
This is the rooted reachable-edge method of [Transport--Memory
Completion, Theorem 66.3][TM-Moore] and [Native Birth Provenance,
Proposition 11.2][NBP-Moore], applied to the present one-root domain.
It does not assume a tree-shaped controller or an acyclic union graph.

If $L=0$, the two admitted sources $T_0,T_1$ return absence at every
nonempty word. Their state paths agree until an empty-word query.
Such a running state must be reached: without it the two runs cannot
terminate at different correct halts. At that state the root is never
absent on any source, so there are at most three actual successors.
Thus $e\le4j-1$, and (AOF.33) sharpens to $N\le3j$. The empty-word
state is required somewhere on this common path, not necessarily at
the initial state. These inequalities give $j\ge J(L,U)$ and at
least $N+J(L,U)$ installed states. Merges, union cycles across different
source runs, repeated queries, early halts and unused states are all
included. On a single stationary source, revisiting a running state
would repeat its deterministic suffix forever; this excludes a loop
on that run without excluding cycles in the union. When $N=1$, one
initial halt outputting $L$ is minimal and has both other prices zero.

For the upper bound use only the actual $E$ and shortest $P_t$ words
of Definition 8.2. The following finite trees specify immutable tables,
not runtime interval or recursion registers. For every integer $r\ge0$
and $l\ge1$, define $\mathsf{Plus}(l,r)$ on $[l,l+3r]$. At $r=0$
it is the halt outputting $l$. At $r\ge1$ put

$$
a=\left\lfloor\frac{r-1}{2}\right\rfloor,
\qquad b=r-1-a,\qquad t=l+3a+1.
\tag{AOF.34}
$$

Its root queries the materialized shortest $P_t$ word and has the four
successors

| Actual reply | Successor of $\mathsf{Plus}(l,r)$ |
| --- | --- |
| $\bot$ | $\mathsf{Plus}(l,a)$ |
| $\alpha$ | Halt with fixed output $t$ |
| $\beta$ | Halt with fixed output $t+1$ |
| $\mathsf b$ | $\mathsf{Plus}(t+2,b)$ |

Here $t\ge2$, so no nonexistent $P_1$ is used. By (AOF.24) the four
actual cells are $[l,t-1],\{t\},\{t+1\},[t+2,l+3r]$. The tails
have sizes $3a+1$ and $3b+1$. Induction proves sourcewise correctness,
exactly $r$ running nodes and $3r+1$ distinct numeric halts. Each node
and halt is reached by an actual age in this full interval.

For $r\ge1$, define $\mathsf{Zero}(r)$ on $[0,3r-1]$ using the same
$a,b$ in (AOF.34). If $a\ge1$, its root queries $P_{3a}$, with
successors

| Actual reply | Successor when $a\ge1$ |
| --- | --- |
| $\bot$ | $\mathsf{Zero}(a)$ |
| $\alpha$ | Halt with fixed output $3a$ |
| $\beta$ | Halt with fixed output $3a+1$ |
| $\mathsf b$ | $\mathsf{Plus}(3a+2,b)$ |

The corresponding cells have sizes $3a,1,1,3b+1$. If $a=0$, use
$E$: alpha goes to the halt zero, beta to the halt one, and branch to
$\mathsf{Plus}(2,b)$; the absent entry goes to the existing halt zero.
The absent reply is impossible and the three actual cells have sizes
$1,1,3b+1$. This case includes $r=1$ and $r=2$. Induction gives exactly
$r$ running nodes and $3r$ fixed-output halts, correct throughout the
full interval. There is exactly one $E$ node along its zero-origin
recursion, and all other thresholds are at least three. Every submitted
power of $R$ or $LR^s$ denotes the expanded literal word in its table.

For either tree, if $r\le2^k-1$, then $a,b\le2^{k-1}-1$ at a running
root. Induction gives depth at most $k$; a halt has depth zero, and the
$E$ case has only its positive continuation. For $N\ge2$, set $j=J(L,U)$
and $k=K(L,U)$. The supplied capacities (AOF.25) give

$$
\begin{aligned}
N\le C_k&\Longleftrightarrow
 \left\lceil(N-1)/3\right\rceil\le2^k-1,\\
N\le A_k&\Longleftrightarrow
 \left\lceil N/3\right\rceil\le2^k-1\quad(k\ge1).
\end{aligned}
\tag{AOF.35}
$$

Consequently $j\le2^k-1$. Start with $\mathsf{Plus}(L,j)$ if $L\ge1$,
or $\mathsf{Zero}(j)$ if $L=0$. Its full source interval extends past
$U$ by $d=3j+1-N$ or $d=3j-N$ respectively, with $0\le d\le2$.
Keep its $j$ running states and delete only the $d$ largest output
halts. Redirect every transition to a deleted halt to the retained halt
with output $L$. Such an edge cannot be used on any admitted source:
the full tree was correct, and its state path on that fixed source ends
at that source's own retained halt. Therefore the restricted table has
the same sourcewise state paths and outputs, $j$ running states, exactly
$N$ halts and depth at most $k$. The lower bound already proved forces
every one of these $j$ states to be reached, for otherwise the actual-run
union would have fewer than $J(L,U)$ running vertices. This establishes
(AOF.32) without a pruning or acyclicity assumption about competitors.
Theorem 8.3's call lower bound applies to this table as to any reader,
so its worst calls are exactly $K(L,U)$. No call-capacity formula is
newly derived here.

Finally preserve this exact counted state set while attaining the
supplied peak. For a nonsingleton $U\ge1$, put $m=M(L,U)$ as in
(AOF.29). For each running state $s$, apply Theorem 9.1 to its fixed
word $p_s$, giving the fixed word $q_s$ and total reply map $\phi_s$.
For this tree the supplied choice is explicit. If $U\le2$, use $q_s=E$
and map its alpha, beta and branch replies to the old word's values
at ages $0,1,2$; fill its absent entry arbitrarily. If $U\ge3$, keep
every word of length at most $m$ with the identity map. An overlong
tree word is a shortest $P_t$ with $t\ge2m+1$; use $q_s=R^m$ and

$$
\phi_s(\bot)=\bot,\quad
\phi_s(\alpha)=P_t(2m),\quad
\phi_s(\beta)=P_t(2m+1),\quad
\phi_s(\mathsf b)=P_t(2m+2).
$$

These are fixed values of (AOF.24), the $P$ cases of Theorem 9.1's
supplied map, not new acquisitions. Install in that same state

$$
\operatorname{addr}'(s)=q_s,\qquad
\operatorname{next}'(s,a)=\operatorname{next}(s,\phi_s(a)).
\tag{AOF.36}
$$

Keep the initial state, state partition and fixed halt outputs. The
four entries of this new transition row contain the composed successor
indices; no decoded reply, decoder state or external register is used.
For each admitted $n$, (AOF.28) says precisely
$r_{T_n}(p_s)=\phi_s(r_{T_n}(q_s))$. Induction along this fixed source's
run therefore preserves its entire state sequence, halt and call count.
One genuine paid call replaces one call, including when $q_s=E$.
The raw reply belongs to $q_s$, and is not asserted to be a receipt at
$p_s$. All new words have length at most $m$. Theorem 9.2's independent
peak lower bound forces the maximum to be exactly $M(L,U)$.

This uses the paid state-local response-recoding method already supplied
by [Native Birth Provenance, Theorem 12.3 and (NBP.12.7)][NBP-Moore].
The required native interval correspondence is (AOF.28) on every actual
age in this interval; it is not that theorem's padded inverse-source
correspondence. Because the map depends on the installed state alone,
the composition is also valid for an arbitrary shared graph, regardless
of the history reaching a state. For the constructed table it preserves
all reached states. Thus one table attains all four displayed counts
$J,N+J,K,M$ without combining separate optimizers. $\square$

**Proposition 10.3 (the extra state distinction and its representation
boundary).** For a fixed nonsingleton interval, $N$ complete-output halts
require exactly $J(L,U)$ additional running states in a minimum table.
Compared with a positive interval of the same size, the zero origin
requires one extra running state exactly when $N\equiv1\pmod3$ and
$N\ge4$. An injective fixed-width binary representation of the complete
minimum state set needs and admits $\lceil\log_2(N+J(L,U))\rceil$ bits.
This width excludes the immutable literal, transition and output tables.

On $[0,3]$ there are two running states and four halts: one state reads
$E$, sends alpha and beta to outputs zero and one, and sends branch to
the second state, which reads $R$ and sends alpha and beta to outputs
two and three. Fill the remaining entries with the halt zero. On $[1,4]$
one running state reads $R$ and sends absent, alpha, beta and branch
directly to the four respective fixed outputs $1,2,3,4$.

Positive intervals $[l,l+1]$, $l\ge1$, have three total states and one
call, while their minimum peak is $\lfloor l/2\rfloor$, unbounded in
$l$. A single finite table with fixed numeric halts cannot identify all
unbounded ages. These state, call and literal-length results impose no
summed-length minimum or physical-memory or physical-time equivalence.

**Proof.** The counts and the two literal examples follow from Theorem
10.2 and (AOF.24). Comparing the two ceilings in (AOF.31) gives the
stated residue class; the singleton is separately one halt. An injective
$w$-bit state encoding exists exactly when $2^w\ge N+J(L,U)$.
The translation claim is Theorems 8.3 and 9.2 at $N=2$. Its address
constants and output integers vary with $l$, so their representation
costs are not bounded by three abstract states. Finally a fixed finite
halt set has finite output image, whereas unbounded ages require an
infinite image. $\square$

**Mathematical citation 10.4 (source-specific content and reused methods).**
Definitions 8.1--8.2 and Theorems 8.3, 9.1--9.2 at the immutable source
[1f90f2ec304615c711e1ab2cdef401881881fcc9](https://github.com/the-omega-institute/trureturing/blob/1f90f2ec304615c711e1ab2cdef401881881fcc9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md#8-stationary-interval-reading-with-a-zero-origin)
supply the stationary interval contract, actual guarded query partitions,
legal shortest words, call capacities and bounded-query reply refinement.
Their ARH/JRF/SLH suppliers retain the scopes specified there. The
rooted-edge count is the existing TM66.3/NBP11.2 method. The fixed-address,
complete-output Moore convention and paid shared-state recoding are
[NBP, Definitions 11.1, 12.1--12.2, Theorem 12.3 and Proposition
12.5][NBP-Moore] at immutable revision
$\mathtt{0ec296c8f9cfd78898ea44f5faf5d1eaa49aa656}$.

In NBP12 the target is a whole predecessor row on an actual one-image
fiber, with acquired exported initialization and a class-root task.
Here there is one common initial state, $N$ distinct numeric outputs,
and the reply identity holds on every declared actual $T_n$. That
identity validates the same state-local transition composition; no
inverse-fiber numerical frontier, advice optimization or arbitrary
fixed-encoder theorem is transferred. Generic shared-graph recoding,
rooted counting and the existing $K/M$ formulas are attributed supply.
The repo-derived content is the interval-specific sharp $J,N+J$ bound,
its obligatory three-reply root defect and the all-size native tree
realizing that bound at the supplied optimal call depth and peak.

Classical state-associated output terminology is attributed to Edward
F. Moore, *Gedanken-Experiments on Sequential Machines*, *Automata
Studies*, [DOI:10.1515/9781400882618-006](https://doi.org/10.1515/9781400882618-006).
This is bibliographic attribution; no external minimization theorem is
a premise. For the distinction between allowed query geometry and
decision-tree depth compare Nowak's primary text cited in Mathematical
citation 9.4, especially §§II-A and V-A. Its binary-query bounds supply
none of the present state constants or common witness. These scoped
correspondences make no worldwide novelty or priority claim.

[TM-Moore]: https://github.com/the-omega-institute/trureturing/blob/1f90f2ec304615c711e1ab2cdef401881881fcc9/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM66-T3
[NBP-Moore]: https://github.com/the-omega-institute/trureturing/blob/0ec296c8f9cfd78898ea44f5faf5d1eaa49aa656/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#12-exact-joint-record-total-moore-state-and-call-transfer-on-every-full-fiber

## 追加锚（本行以下为增补区）
