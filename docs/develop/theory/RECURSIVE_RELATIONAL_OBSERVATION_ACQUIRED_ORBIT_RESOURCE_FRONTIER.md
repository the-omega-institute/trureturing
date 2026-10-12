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
