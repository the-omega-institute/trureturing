# Finite signed native witness production and non-rational pair contact

## 1. Finite sources and the joint obligation

**Definition 1.1 (native values and prefixes).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

All values are nonempty finite free ordered trees. Repeated occurrences
are retained. At every finite word $p$ over $\{L,R\}$, the original
reply $r_u(p)$ is $\alpha,\beta,\mathsf{branch}$ or $\mathsf{absent}$.
The root word is $\varepsilon$; strict descendants of leaves are absent.
Put

$$
u\equiv_h v\iff\forall |p|\le h\quad r_u(p)=r_v(p),
\qquad
\delta(u,v)=\min\{|p|:r_u(p)\ne r_v(p)\},
\tag{SPC.1}
$$

with $\delta(u,u)=\infty$. Thus inclusive agreement through $h$ means
$\delta(u,v)>h$. The operation $\rho$ is interpreted, not a free unary
constructor.

**Definition 1.2 (entire acquired input).** Use [ARH, Definitions 1.1–1.2
and Assumption 1.3][ARH]. Finite original cuts $P,Q$ are prefix-free.
A complete row retains its entire concrete exterior, reached holes and
whole-subtree equality partition. Every old repeated class and every
different-class disequality remains imposed, including off-task classes.
The entire fiber is

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{SPC.2}
$$

A record $(a,s,b,t,\bowtie)$, with $\bowtie\in\{=,\ne\}$, requires
both endpoints to be reached in $\rho^a u,\rho^b u$ and compares their
entire subtrees. Absence invalidates either sign. Histories are finite
lists, with repetitions, all concerning the same original source.

**Definition 1.3 (mixed pieces and a prescribed pair).** Use the mixed
grammar of [NIC, Definition 1.2][NIC]:

$$
A::=g\mid T_{n_i+c}\mid\rho^a z_j\mid\langle A,A\rangle,
\qquad T_n=\rho^n\alpha,\qquad a,c\in\mathbb N.
\tag{SPC.3}
$$

Here $g$ is fixed and finite, and arguments range over the entire
$\mathbb N^k\times\mathcal T^m$. Named occurrences share values.
All comparisons are after native expansion.

Fix different complete finite $Q$-row labels $r_0,r_1$ and supplied
pieces $(U_i,C_i)$ such that

$$
C_i(\theta_i)\Longrightarrow
U_i(\theta_i)\in D\ \land\ R_Q(U_i(\theta_i))=r_i.
\tag{SPC.4}
$$

Each $U_i$ is mixed. Each $C_i$ is a finite Boolean combination of
Presburger conditions, mixed native equalities and supplied fixed
navigation or complete-row tests, retaining the entire old input,
both signed guards and every exact new row bit. [NIC, Theorem 4.3][NIC]
supplies such pieces with a finite cover of each stratum. A directly
proved exact stratum description also supplies (SPC.4). Define

$$
J(h)\iff\exists\theta_0,\theta_1\quad
C_0(\theta_0)\land C_1(\theta_1)\land
U_0(\theta_0)\equiv_h U_1(\theta_1).
\tag{SPC.5}
$$

The two tuples are independent here. A witness description may couple
them without changing either source domain. They are mathematical
parameters, not observations available to a physical service.

## 2. A finite productive signed certificate

**Definition 2.1 (certificate data).** Combine the two parameter tuples
and any finite auxiliary tuple into $\theta=(\mathbf n,\mathbf z)$.
Supply a finite Boolean invariant
$I(\theta)=C_0(\theta_0)\land C_1(\theta_1)\land\Theta(\theta)$
in the language of Definition 1.3. Supply a simultaneous substitution
$S$ sending each natural coordinate to $n_i+d_i$, for fixed $d_i\ge0$,
and each tree coordinate to a mixed template in the old $\theta$.
It sends every finite assignment to a finite assignment.

Supply finitely many mixed comparison pairs $A_j(\theta),B_j(\theta)$,
with $A_0=U_0,B_0=U_1$. For each $j$ supply a common template

$$
H_j(\theta;\mathbf w)::=E(\theta)\mid\rho^a w_k\mid
\langle H,H\rangle,
\tag{SPC.6}
$$

where $E$ is mixed and $a\ge0$ is fixed. Comparison holes may repeat.
The same coefficient values $E(\theta)$ occur on both sides.
Require the finite obligations

$$
\begin{aligned}
&\exists\theta\ I(\theta),\qquad I(\theta)\Longrightarrow I(S\theta),\\
&I(\theta)\Longrightarrow A_j(S\theta)=H_j(\theta;\mathbf A(\theta)),\\
&I(\theta)\Longrightarrow B_j(S\theta)=H_j(\theta;\mathbf B(\theta)).
\end{aligned}
\tag{SPC.7}
$$

Each occurrence $\rho^a w_k$ in $H_j$ gives an edge $j\to k$,
weighted by $d+\lfloor a/2\rfloor$, where $d$ is its address length
in the displayed pairing skeleton. Count occurrences separately.
Keep the vertices reachable from $0$, and let their number be $r\ge1$.
Require that their zero-weight edges contain no directed cycle.
A hole-free template has no outgoing edges. This is supplied finite
certificate data, not an asserted finite quotient of arbitrary histories.

**Theorem 2.2 (verification and actual finite witnesses).** Validity of
Definition 2.1, with the fixed input and pieces of Definition 1.3,
has a terminating mathematical decision. A valid
certificate supplies a finite seed $\theta^*$ such that

$$
\theta_h=S^{r(h+1)}\theta^*
\tag{SPC.8}
$$

witnesses $J(h)$ for every $h\ge0$. Both complete signed predicates and
both exact finite row labels hold at every iterate. No completeness
of this sufficient certificate language is asserted.

Proof. Fixed powers distribute through pairing, act on finite grounds,
send $T_{n_i+c}$ to $T_{n_i+c+a}$ and add their fixed exponents on
residual occurrences. Substitution by $S$ therefore preserves mixed
syntax; natural increments preserve Presburger formulas. Navigation
and row tests still use supplied finite addresses and cuts.

The source/row inclusions (SPC.4), if not supplied by the owning
piece theorem, are themselves checked by the counterqueries
$C_i(\theta_i)\land[U_i(\theta_i)\notin D]$ and
$C_i(\theta_i)\land[R_Q(U_i(\theta_i))\ne r_i]$.
The whole predicate (SPC.2) and the fixed complete row are finite
tests of the same language after substitution. This checks the
needed forward inclusions; no completeness of a proposed whole
cover is required for a sufficient witness certificate.

The seed query, the preservation counterquery
$I(\theta)\land\neg I(S\theta)$, and every intertwining counterquery
$I(\theta)\land[A_j(S\theta)\ne H_j(\theta;\mathbf A(\theta))]$
or its $B$ counterpart are finite native queries with designated
natural scalars. Apply [NSF, Lemma 5.1 and Theorem 5.2][NSF],
the scalar-preserving extension in [URR, Corollary 3.2, proof][URR],
and the variable-rank navigation cases of [NIC, Proposition 5.3,
proof][NIC]. Explicit atomic definitions retain the designated scalars
through the finite branches; auxiliary ranks are existentially
quantified in the resulting Presburger systems. The supplier reconstructs
finite native witnesses. This uses its parameter-preserving query
decision, not a Cartesian-domain assumption on $I$. Complements of
guarded predicates and native negative records retain their different
meanings. Only finitely many queries and a finite zero-edge cycle test
are required.

For prefix growth use [NLC, Lemma 3.1][NLC]:
$\mu(T_n)=\lfloor n/2\rfloor$, where $\mu$ is minimum leaf depth.
Every $\rho^a t$ has no leaf above depth $\lfloor a/2\rfloor$:
its original leaves expand to $T_a$ or $T_{a+1}$ under their original
paths. Consequently

$$
\delta(\rho^a s,\rho^a t)\ge\delta(s,t)+\lfloor a/2\rfloor.
\tag{SPC.9}
$$

Indeed a first discrepancy of finite depth $D$ cannot have an absent
endpoint, since that would give an earlier leaf/branch discrepancy
at an ancestor. Before $D$, common original branches and leaves match.
Common leaves expand identically, including identical absent descendants.
At depth-$D$ reached discrepancies, both expanded subtrees have only
branches at depths less than $\lfloor a/2\rfloor$. No discrepancy
can therefore occur before $D+\lfloor a/2\rfloor$. Equal inputs
give equal expansions, with $\infty+c=\infty$.

Identical coefficients in (SPC.6) contribute no discrepancy. A hole
path adds its displayed depth, so

$$
\delta(H_j(\theta;\mathbf s),H_j(\theta;\mathbf t))
\ge\min_{e:j\to k}(w_e+\delta(s_k,t_k)).
\tag{SPC.10}
$$

An empty minimum is $\infty$. Put $\theta_t=S^t\theta^*$ and
$D_j(t)=\delta(A_j(\theta_t),B_j(\theta_t))$. Invariance proves
$I(\theta_t)$ by induction. The intertwining identities give

$$
D_j(t+1)\ge\min_{e:j\to k}(w_e+D_k(t)).
\tag{SPC.11}
$$

Initially every $D_j(0)\ge0$. Iteration bounds $D_0(t)$ below by
the minimum weight of a length-$t$ walk from $0$, or $\infty$
if no such walk exists. Every block of $r$ edges contains a
positive-weight edge: otherwise its $r+1$ vertices would repeat a
vertex among $r$ possibilities and yield a zero-weight directed cycle.
Integer nonnegative weights thus give $D_0(t)\ge\lfloor t/r\rfloor$.
At $t=r(h+1)$ this is greater than the inclusive $h$. Both complete
$C_i$ hold at that finite assignment; (SPC.4) reconstructs sources
in the unchanged entire $D$ with exactly $r_0,r_1$. All signed
records, guards, old class relations and row bits hold on each finite
source. No sign is inferred from an infinite limit. $\square$

## 3. An entire acquired copied-source consumer

**Definition 3.1 (shifted constructor family).** Let $C$ be any finite
original constructor context with exactly one hole at address $w$,
of length $d\ge1$. All other parts are fixed finite native trees.
Fix $a\ge1$, and put

$$
F(y)=C[\rho^a y],\qquad
U(x,y)=\langle x,\langle y,F(y)\rangle\rangle.
\tag{SPC.12}
$$

Use the old root cut $P=\{\varepsilon\}$ and its complete one-hole row.
Retain epoch-zero branch literals at $\varepsilon,R$, and at every
displayed branch of $C$ prefixed by $RR$. Retain the exact epoch-zero
label at every displayed concrete leaf of $C$, also prefixed by $RR$.
The hole $RRw$ has no literal. Retain both records

$$
(a,RL,0,RRw,=),\qquad (0,RL,0,RR,\ne).
\tag{SPC.13}
$$

All listed occurrences, including repetitions, remain in the input.
The target cut is $Q=\{L,RL,RR\}$.

**Theorem 3.2 (entire fiber and every complete row label).** The retained
input has exactly the entire original fiber

$$
D_C=\{U(x,y):x,y\in\mathcal T\}.
\tag{SPC.14}
$$

Its complete $Q$-row image has exactly three labels, with reached set
$Q$ and exterior $\langle\square_1,\langle\square_2,\square_3\rangle\rangle$:

$$
\begin{aligned}
r_0&:\{\{1,2\},\{3\}\},&
D_0&=\{U(y,y):y\in\mathcal T\},\\
r_1&:\{\{1,3\},\{2\}\},&
D_1&=\{U(F(y),y):y\in\mathcal T\},\\
r_2&:\{\{1\},\{2\},\{3\}\},&
D_2&=\{U(x,y):x\ne y,\ x\ne F(y),\ x,y\in\mathcal T\}.
\end{aligned}
\tag{SPC.15}
$$

These are the exact whole strata. Under ARH Assumption 1.3's paid
producer and complete-cut premises, the input is authentically
acquirable at any common final epoch $N\ge a$.

Proof. The literals force
$u=\langle x,\langle y,C[z]\rangle\rangle$ and every strict hole
ancestor to be a branch, so $RRw$ is reached. Root and $R$ branches
survive $\rho^a$, and the whole subtree at epoch-$a$ address $RL$
is $\rho^a y$. The positive record says $z=\rho^a y$.

Write $\ell(t)$ for finite leaf count. Native $\rho$ does not
decrease it: alpha becomes one leaf, beta becomes two, and pairing
adds counts. Since the hole is proper, $C$ has $b_C\ge1$ concrete
leaves outside it. Thus

$$
\ell(F(y))=b_C+\ell(\rho^a y)>\ell(y).
\tag{SPC.16}
$$

The negative $y\ne F(y)$ holds for every finite $y$, with both
original endpoints reached. Conversely each displayed $U(x,y)$
satisfies the old root row, all literals and both records with both
guards. This proves both entire-source inclusions, retaining the
negative record rather than deleting it as redundant.

At $Q$ the whole subtrees are $x,y,F(y)$ and the last two differ.
Their possible partitions and exact conditions are precisely (SPC.15).
The first two are attained for every $y$ by the displayed sources.
The third is attained by $y=\alpha,x=\beta$, since $F(\alpha)$ is
a branch. The whole exterior and reached set are fixed throughout;
no extra label or exterior is omitted.

For acquisition apply [ARH, Proposition 2.1][ARH] with these public
literal coordinates, endpoint pairs, $P,N$. Its source-total paid
epoch-ordered procedure acquires finite whole-subtree descriptions,
computes the signs, and retains exactly the canonical input after the
stipulated complete cut. Conversely every source satisfying the fixed
replies and signs yields that same retained state. All other accessible
source-dependent fields must be included in the cut. Acquisition is
finite separately on each finite source; no uniform cost is asserted.
These are exactly the supplier's producer hypotheses. $\square$

**Theorem 3.3 (productive certificate for the prescribed pair).** The
exact pieces $U_0(z_0)=U(z_0,z_0)$ and $U_1(z_1)=U(F(z_1),z_1)$,
with independent residuals ranging over all of $\mathcal T$, admit
Definition 2.1's certificate. Their prescribed $J(h)$ has actual
finite witnesses at every inclusive depth $h$.

Proof. Theorem 3.2 supplies both inclusions for each exact stratum
and all complete signed predicates. Their only nontrivial negative
is $z_i\ne F(z_i)$, valid on every finite assignment by (SPC.16).
Couple witnesses by $z_0=z_1$, and take

$$
\begin{aligned}
S(z_0,z_1)&=(F(z_0),F(z_1)),\qquad \theta^*=(\beta,\beta),\\
A_1&=z_0,\qquad B_1=F(z_1),\\
H_1(\theta;\mathbf w)&=F(w_1),\\
H_0(\theta;\mathbf w)&=
\langle F(w_1),\langle F(z_0),F^2(z_0)\rangle\rangle.
\end{aligned}
\tag{SPC.17}
$$

These are mixed templates. The coupling is nonempty and preserved.
Every finite iterate satisfies the complete piece predicates.
For comparison $1$, substitution gives $F(z_0),F^2(z_1)$, exactly
the two $H_1$ values. For comparison $0$, substitution gives
$\langle F(z_0),\langle F(z_0),F^2(z_0)\rangle\rangle$ and
$\langle F^2(z_1),\langle F(z_1),F^2(z_1)\rangle\rangle$.
They are the corresponding $H_0$ values because $z_0=z_1$.
The graph has edges $0\to1$ of weight $1+d+\lfloor a/2\rfloor$
and $1\to1$ of weight $d+\lfloor a/2\rfloor$, both positive.
Theorem 2.2 applies.

Explicitly, put $y_0=\beta,y_{t+1}=F(y_t)$ and

$$
u_t^0=U(y_t,y_t),\qquad u_t^1=U(y_{t+1},y_t).
\tag{SPC.18}
$$

The hole depth and (SPC.9) give, with $b=d+\lfloor a/2\rfloor$,
$\delta(F(s),F(t))\ge\delta(s,t)+b$; hence
$\delta(y_t,y_{t+1})\ge tb$. The two $U$ sources share their
entire right subtree and differ only below $L$, so their discrepancy
is at least $1+tb$. Taking $t=h+1$ suffices. Both exact finite
labels remain $r_0,r_1$, and all retained records hold at each stage.
No partition is assigned to a limit. $\square$

## 4. The unique non-rational contact

**Definition 4.1 (completion and comparison classes).** Let
$\widehat{\mathcal T}$ contain all valid finite or infinite ordered
native trees, with two children at every branch and no children at
leaves. The four replies extend to it. A point belongs to $\overline X$,
for $X\subseteq\mathcal T$, when each of its supplied finite inclusive
prefixes is realized by a member of $X$. This definition imposes no
signed predicate or finite row partition on a limit.

A rational native tree has finitely many distinct whole subtrees,
including finite trees [Comon–Lescanne, §2][CL]. Let $\Omega$ be the
all-branch tree. A fixed-residual section is
$\{A(\mathbf n,\mathbf z^*):\mathbf n\in S\}$ for one finite mixed
source template, one fixed finite native tuple $\mathbf z^*$, and
any subset $S$ of its finite-dimensional natural rank space.
No effective or Presburger hypothesis on $S$ is imposed.

**Theorem 4.2 (unique contact and its rationality boundary).** For
Definition 3.1's context and $a\ge1$ there is a unique completion tree
$K$ with $K=C[\rho^a K]$. Put $L_C=\langle K,\langle K,K\rangle\rangle$.
Then

$$
\overline{D_0}\cap\overline{D_1}=\{L_C\}.
\tag{SPC.19}
$$

Both $K,L_C$ are non-rational in the native signature. With the same
proper one-hole context and $a=0$, the unique fixed point is rational.

Proof. Extend $\rho^a$ by retaining original branches and replacing
each reached leaf by its finite native image, including along infinite
branch paths. Original-prefix locality proves continuity. The proof of
(SPC.9) applies in this completion too: a subtree without leaves has
only branches, so satisfies the same lower bound. The common context
gives at least $d$ levels of prefix gain.

Consecutive iterates $F^t(s),F^{t+1}(s)$ of any finite seed agree below
$td$. Transitivity along later consecutive iterates shows stabilization
of every finite reply. The stable replies define a valid tree: root
reachability, both children of a branch, and absence below a leaf each
concern finitely many coordinates and hold in eventually matching
finite trees. Continuity gives $F(K)=K$. Two fixed points, starting
with vacuous agreement below zero, agree below $td$ after $t$
applications of the same gain. They agree at every address and are equal.
Every seed orbit therefore has this same limit.

This is the ordinary guarded fixed-point argument. Interpreted recursive
schemes and metric solutions are mature background [Milius–Moss,
Theorems 7.5 and 7.15][MM]; no new general fixed-point theorem is claimed.

A common closure point retains the outer skeleton; write its three
subtrees $x,y,z$. From $D_0$ it inherits $x=y,z=F(y)$, and from
$D_1$ it inherits $x=F(y),z=F(y)$. Whole-tree equality is closed:
a discrepancy would occur at a finite address and contradict equal
sufficiently close approximants. The graph of $F$ is closed by its
continuity. Thus $y=F(y)$, so $x=y=z=K$. Conversely (SPC.18)
converges on every finite prefix to $L_C$. This proves both inclusions
of (SPC.19) without treating finite disequality as closed.

Let $q$ be the sibling of the first edge of $w$. The side tree
$g=C|_q$ is finite and nonempty. Branches on the hole path survive
every fixed iterate. Distribution through $C$ proves by induction

$$
K|_{w^j}=\rho^{aj}K,\qquad K|_{w^jq}=\rho^{aj}g\quad(j\ge0).
\tag{SPC.20}
$$

Indeed in $\rho^{aj}C[\rho^a K]$ the path $w$ stays intact, its
hole becomes $\rho^{a(j+1)}K$, and its side at $q$ becomes
$\rho^{aj}g$. These are expanded native subtrees, not trees carrying
a unary $\rho$ label.

Every leaf of $g$ expands to $T_{aj}$ or $T_{aj+1}$ under its
original path. Thus $\mu(\rho^{aj}g)\ge\lfloor aj/2\rfloor\to\infty$.
A finite set of finite trees has bounded minimum leaf depth.
Equation (SPC.20) consequently supplies infinitely many distinct
finite subtrees. Both $K$ and $L_C$ are non-rational.
For $a=0$, the finite directed constructor graph of $C$, with its
hole pointing back to its root, unfolds to the unique fixed point.
Its finitely many vertices represent all subtree values, so that point
is rational. The positive shift is essential. $\square$

**Theorem 4.3 (finite fixed-completion boundary).** Every closure point
of a finite union of fixed-residual sections is a finite original
constructor context filled by finite trees and $\Omega$, and is
therefore rational. No finite union of such sections inside $D_0$
and finite union inside $D_1$ can jointly retain actual finite witnesses
with arbitrarily long common prefixes for this prescribed pair.

Proof. Choose finite members agreeing with a closure point through
increasing depths. One of the finitely many sections occurs on an
infinite subsequence. Successively select subsequences in each of its
finitely many natural coordinates on which the coordinate is constant
or tends to infinity. Either some value occurs infinitely often, or
every finite initial set occurs only finitely often. This selection
works for arbitrary $S$ and respects every relation encoded in $S$.

Grounds and decorated fixed residuals stay finite. Constant ranks give
fixed atoms; divergent ranks give $T_{n_i+c}\to\Omega$ by NLC Lemma
3.1. Induction on the finite mixed template gives the stated context
limit, equal to the chosen closure point. Its distinct subtrees come
from finitely many context nodes, finitely many finite filling nodes,
and the one value $\Omega$. It is rational. No sign was passed to
the limit.

Now suppose the two designated subfamilies provided pairs agreeing
through depths tending to infinity. Select section indices on both
sides, then constant-or-divergent subsequences for their coordinates
together. The same argument gives rational limits on both sides.
The unbounded agreements force the limits to be identical, and section
membership puts that point in both closures. It must be the
non-rational $L_C$ by (SPC.19), a contradiction.

More generally (SPC.19) excludes any certificate for this pair whose
soundness requires a rational native common closure point. Rationality
is measured after expansion in $\{\alpha,\beta,\langle\ ,\ \rangle\}$.
It excludes neither the finite interpreted equation $K=C[\rho^a K]$,
the varying finite residual production (SPC.18), nor another proved
encoding. $\square$

## 5. Actual service consequence and containment

**Theorem 5.1 (inherited paid-service obstruction).** Under ARH
Assumption 1.3 on the entire $D_C$, no deterministic effective legal
source-total service for $R_Q$ has a uniform finite new-read bound,
including adaptive arbitrary-finite-word reads, same-register forward
updates and variable absorbing halt.

Proof. Such a service would give a finite inclusive original determining
depth by [ARH, (ARH.2.3)][ARH]. Theorem 3.3's finite counterpair at that
depth has the same prefix and different exact complete rows in the same
entire acquired fiber, a contradiction. All supplier hypotheses are
retained: one original root, authentic $N\ge a$, paid acquisition and
complete accessible-state cut. The witness iteration is offline
mathematical counterinput production. It gives the service no rank,
chart, equality, reset, clone, reroot or identity port. This is a
supplier application, not a new action/resource optimum. $\square$

**Theorem 5.2 (requirements and pair-specific scope).** Dropping
productivity or complete signed preservation invalidates the certificate
conclusion. A non-rational contact for one pair does not imply that the
entire fiber lacks other finite-context contacts.

Proof. Without productivity, use the two fixed sources
$U(\beta,\beta),U(F(\beta),\beta)$, the identity substitution and
$H_0=w_0$. Seed feasibility, signed preservation and intertwining hold.
The zero-weight self-loop is present. The fixed distinct finite sources
have a finite discrepancy and cannot witness every $h$.

For preservation, set $F(z)=\langle\alpha,\rho z\rangle$, seed
$z=\beta$, and condition $z\ne F(\beta)$. It holds at the seed and
fails after the first substitution $z\mapsto F(z)$. Guarded prefix
gain alone does not preserve even this single negative. Any additional
retained history must enter $I$ in full and have preservation proved anew.

For the final assertion specialize to $C[t]=\langle g,t\rangle$.
For sufficiently large $m$, $T_{m+1}\ne F(T_m)$, since their left
children would otherwise give $T_m=g$, excluded for all sufficiently
large $m$ by atomic rank injectivity. Thus $U(T_m,T_m)$ has exact
label $r_0$ and $U(T_{m+1},T_m)$ exact label $r_2$. Both tend to
$\langle\Omega,\langle\Omega,\langle g,\Omega\rangle\rangle\rangle$,
a finite context filled by $\Omega$, because
$\rho^a T_m=T_{m+a}$. This supplies finite contact witnesses for a
different pair in the same whole fiber. $\square$

**Definition 5.3 (unchanged objectives and open choice).** For each
actual service $A$ and source $u$ retain raw calls $q_A(u)$, actual
post-entry updates $a_A(u)$ and total submitted literal length
$\ell_A(u)$. Keep distinct

$$
b(A)=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),\qquad
W_\lambda(A)=\sup_{u\in D}
(\lambda_q q_A(u)+\lambda_a a_A(u)+\lambda_\ell\ell_A(u)),
\quad\lambda\in\mathbb Q_{\ge0}^3.
$$

Zero weights are allowed. No new optimum for these quantities or for
acquisition, local work, installation, memory, authentication, retention,
invocation or physical time follows from the certificate.

The remaining choice is [NIC, Open problem 5.5][NIC]: for every arbitrary
complete signed pair terminate with a finite exclusion depth or a finite
description of actual finite witnesses at every depth. Theorem 2.2
verifies a supplied sufficient description, proving neither completeness
nor terminating search. Rejection of a certificate does not decide $J$,
recovery or undecidability. The unrestricted action/resource interface
of [CRF, Open problem 9.1][CRF] and [NIC, Open problem 7.2][NIC]
remains a separate obligation.

## 6. Exact suppliers and attribution

**Definition 6.1 (supplier correspondence).** Numbered source statements
are used at the following exact ranges. These are ordinary mathematical
statements; no kernel verification of this volume is asserted.

| Supplier | Use and boundary |
| --- | --- |
| [ARH, §§1–2, 8, 19][ARH] | Same native source, both signed guards, full old row, paid public producer, complete cut and service/prefix bridge. Ordinary constructor equation/disequality graph non-elimination is already supplied. |
| [ABC, §§1–6][ABC] | Atomic recurrence, native shift and all-source representation. Comparisons here follow native expansion; ambient code inequality is not native disequality. |
| [NSF, §§4–5, 9–10][NSF] | Finite Boolean native queries, witnesses and guard-aware row compilation. Forward-closed domains and observable invariant charts have entire-cover, selector and simultaneous-$\rho$ hypotheses. Definition 2.1 instead supplies an offline two-piece witness subset with a general mixed substitution and finite comparison dependencies. |
| [URR, §§1–3, 7][URR] | Same mixed syntax and designated-scalar query extension. Cartesian rank-support sections are not joint-prefix representatives. Theorem 4.3 compares fixed finite residual sections even over arbitrary rank supports. |
| [NPL, Theorem 5.3][NPL]; [NIC, §§3–5][NIC] | Entire finite row-image classification and exact overlapping signed covers. Supplied-depth decision is already covered. The certificate supplies no unique chart, runtime selector or complete stopping choice. |
| [NLC, Lemma 3.1, §§5–9][NLC] | Atomic minimum depth, supplied-context contact and the rational anchored-comb copied row pair. Its $a=0,g=\alpha$ contact lies outside the context-$\Omega$ language. The positive-shift side ladder excludes every rational native contact for the prescribed pair. Other pairs can still have context contact. |
| [NFO, §§3, 8][NFO] | Fixed-depth/budget obstruction with the unrestricted stopping question retained. Finite samples and cutoffs do not supply (SPC.8)'s all-depth witnesses. |
| [CAR, §§2–4, 6, 10][CAR]; [CRF, §§1, 4–6, 9][CRF] | Cycle-forced atomicity and recognized constructor interfaces retain their exact domains. No atomicity certificate or chart completeness is assumed for an arbitrary signed pair. |
| [GRS, §§1–5, 9][GRS]; [SRF, §§1–3, 6][SRF] | Graph and synchronous arbitrary-word interfaces and distinct objectives. An offline contact description does not create a global physical-action language. |
| [TPO, §§4–5][TPO] | The scoped normal-domain interpretation obstruction is neither a native impossibility theorem nor bypassed by treating $\rho$ as free. |
| [IDC, §§1, 3–5][IDC] | Positive intrinsic-depth leaf-cone costs and depth-two singleton certification concern entire raw-history depth fibers, not two signed row strata's joint prefixes. |
| [CAL, §§4–7][CAL] | Paid full-tree preparation, unknown-lag calibration and its retained cut have right-spine-only later competitors. No retained defect or clock is supplied here. |

**Definition 6.2 (literature and new deduction).** Rationality as finite
subtree diversity and guarded interpreted recursion are mature ideas.
[Comon–Lescanne][CL], *Equational Problems and Disunification*, Journal
of Symbolic Computation 7 (1989), 371–425,
DOI 10.1016/S0747-7171(89)80017-3, §2 and Theorem 1, treats
rational trees over a free signature. Section 6.2 explicitly restricts
transfer of its preceding free-term results to nontrivial equational
theories. No free occurs-check is applied to native interpreted feedback.

[Milius–Moss][MM], *The Category Theoretic Solution of Recursive Program
Schemes*, arXiv:0904.2385v2, Theorem 7.5, supplies interpreted solutions
for guarded schemes in Elgot algebras, unique in completely iterative
algebras. Section 7.3 and Theorem 7.15 concern nonempty complete metric
algebras and contracting functors. This is literature-attested background.
The finite native algebra is not assumed to have those completion
properties; Theorem 4.2 constructs its needed completion and approximants.

The repo-derived increment combines the productive signed comparison
mechanism with its exact acquired copied-source consumer, the unique
non-rational native contact for every proper shifted one-hole context,
and the arbitrary-support finite-fixed-section obstruction. Seed,
invariant and productive comparison identities are separate obligations;
ordinary contraction does not supply them. Every actual finite sign
and full row is retained. Fixed-point existence, native feasibility,
rank-support completion, constructor graph non-elimination and the
earlier rational comb obstruction keep their original ownership.
No external priority, literature-wide originality, implemented solver,
undecidability or empirical learning conclusion is asserted.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NFO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_OBSTRUCTION.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[CRF]: RECURSIVE_RELATIONAL_OBSERVATION_CONSTRUCTOR_RESOURCE_FRONTIER.md
[GRS]: RECURSIVE_RELATIONAL_OBSERVATION_GRAPH_RESOURCE_SEPARATION.md
[SRF]: RECURSIVE_RELATIONAL_OBSERVATION_SYNCHRONOUS_RESOURCE_FRONTIER.md
[TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[IDC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_INTRINSIC_DEPTH_CERTIFICATES.md
[CAL]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[MM]: https://arxiv.org/pdf/0904.2385v2

## 追加锚（本行以下为增补区）
