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

## 7. Exact comparison of closed native presentations

**Definition 7.1 (closed defining subsystem).** A closed presentation has
finitely many named states $X_1,\ldots,X_m$ and one supplied definition

$$
X_i=\langle E_i,F_i\rangle\qquad(1\le i\le m).
\tag{SPC.21}
$$

Expressions have finite syntax built from finite native grounds,
$\Omega$, ordered pairing and $\rho^kX_j$, with fixed numeral $k\ge0$.
Powers on compound expressions can first be distributed and evaluated
on grounds; $\rho^k\Omega=\Omega$. Every state occurrence is under the
displayed pair guard. Explicitly supplied finite ground definitions may
be inlined before (SPC.21); no unspecified root-link normalization is
assumed. There are no unknown free tree values or uninstantiated ranks.
Repeated occurrences of a state denote one whole value.

The presentation may retain finitely many further positive equations
$A_l(\mathbf X)=B_l(\mathbf X)$ and image filters
$C_l(\mathbf X)\in L_{s_l}$, where
$L_s=\rho^s[\widehat{\mathcal T}]$ and each $s_l$ is a fixed numeral.
The equations selected for (SPC.21) form a defining subsystem, not a
choice between alternative productions. They must define every variable
of every retained expression. All other equations and filters are
conjuncts on its single generated valuation.

**Theorem 7.2 (native two-argument grammar comparison).** The subsystem
(SPC.21) has a unique completed valuation $\mathbf K$. Every expression
in that valuation has an effective finite ground initial term in one
finite deterministic first-order grammar. Its action semantics preserves
every original-address reply, including absence. Equality of any two
such expressions is decidable. For each fixed compiled grammar and
fixed pair of initial terms one can compute a depth $H$ such that
unequal native values already disagree at an original address of length
at most $H$.

Proof. The guarded existence and uniqueness argument is the one used
in Theorem 4.2, now on a finite product. Matching original prefixes
remain matching under every fixed native power. Pairing gains one
level, so simultaneous iteration stabilizes every finite prefix
independently of the seed and yields exactly one valuation. This is
reuse of guarded interpreted recursion, not a new fixed-point principle.

For completed native $a,b,t$, let $H_{a,b}(t)$ replace each alpha leaf
of $t$ by $a$, each beta leaf by $b$, and preserve its ordered branches
and infinite paths. Define finite two-variable constructor terms

$$
P_0(a,b)=a,\qquad P_1(a,b)=b,\qquad
P_{k+2}(a,b)=\langle P_{k+1}(a,b),P_k(a,b)\rangle.
\tag{SPC.22}
$$

In particular $P_k(\alpha,\beta)=T_k$. The two actual leaf laws,
distribution through ordered pairs and composition of leaf replacement
give

$$
H_{a,b}(\rho^k t)
 =H_{P_k(a,b),P_{k+1}(a,b)}(t).
\tag{SPC.23}
$$

For finite $t$ this follows by structural induction, with
$H_{a,b}(\rho\alpha)=b$ and
$H_{a,b}(\rho\beta)=\langle b,a\rangle$ as its two leaf cases.
Iterating these cases gives (SPC.22). For a completed $t$, fill its
successively deeper frontiers by finite leaves. Each fixed original
prefix of either side stabilizes to the same reply as the corresponding
finite replacement: neither native update nor leaf replacement changes
an already specified branch prefix. Thus (SPC.23) holds also on infinite
branches and on mixed finite/infinite trees. In particular
$H_{a,b}(\Omega)=\Omega$. This identity is an intermediate operation
correspondence, not a separate leaf-language representation result.

Use ranked grammar symbols $\mathsf P$ of arity two, $G_i$ of arity
two, and $\mathsf a,\mathsf b,\mathsf O,\mathsf D$ of arity zero.
Translate expressions with two formal variables $a,b$ by

$$
\begin{aligned}
\tau_{a,b}(\alpha)&=a,&
\tau_{a,b}(\beta)&=b,&
\tau_{a,b}(\Omega)&=\mathsf O,\\
\tau_{a,b}(\langle A,B\rangle)
 &=\mathsf P(\tau_{a,b}(A),\tau_{a,b}(B)),\\
\tau_{a,b}(\rho^kX_j)
 &=G_j(P_k(a,b),P_{k+1}(a,b)).
\end{aligned}
\tag{SPC.24}
$$

Here and below the $P_k$ in grammar terms use $\mathsf P$ in place
of native pairing; a finite ground is translated by its finite tree.
Introduce the rules

$$
\begin{aligned}
G_i(a,b)&\xrightarrow{L}\tau_{a,b}(E_i),&
G_i(a,b)&\xrightarrow{R}\tau_{a,b}(F_i),\\
\mathsf P(a,b)&\xrightarrow{L}a,&
\mathsf P(a,b)&\xrightarrow{R}b,\\
\mathsf O&\xrightarrow{L}\mathsf O,&
\mathsf O&\xrightarrow{R}\mathsf O,\\
\mathsf a&\xrightarrow{o_\alpha}\mathsf D,&
\mathsf b&\xrightarrow{o_\beta}\mathsf D.
\end{aligned}
\tag{SPC.25}
$$

The sink $\mathsf D$ has no rules. There are no other rules.
The initial term for $A$ is
$S_A=\tau_{\mathsf a,\mathsf b}(A)$.
All powers are fixed before translation, so every $P_k$, rule and
initial term is finite. Expanding (SPC.22) is sufficient for this
finiteness assertion; no succinctness bound is required.

To verify the semantics, interpret $\mathsf P$ as pairing,
$\mathsf a,\mathsf b$ as the two leaves, $\mathsf O$ as $\Omega$,
and $G_i(A,B)$ as $H_{\llbracket A\rrbracket,\llbracket B\rrbracket}(K_i)$.
Identity (SPC.23) gives
$\llbracket\tau_{a,b}(E)\rrbracket=H_{a,b}(E(\mathbf K))$
after substituting any interpreted arguments. Consequently each $L$
or $R$ rule returns exactly the corresponding whole native subtree.
The only configurations reachable by $L,R$ from an initial term have
either a branch with enabled actions $\{L,R\}$, an alpha leaf with
enabled action $\{o_\alpha\}$, or a beta leaf with enabled action
$\{o_\beta\}$. The sink is reached only after an observation marker.

Induction on an address $p$ now proves: an $L,R$ path labelled $p$
exists exactly when the native node at $p$ is reached, and its
configuration has exactly that node's native label. If a leaf blocks
the path, $p$ and all its extensions are absent. Thus the correspondence
includes all four replies, rather than just reached leaf labels.
The order of $L,R$ is fixed, and every occurrence of $X_i$ still uses
the same $K_i$, even when its two leaf-image arguments differ.

The grammar has the precise rule format of [Jančar, §2, (3)][FOG]:
$A(x_1,\ldots,x_n)\xrightarrow{c}E$, with finite ranked alphabet,
finite action alphabet, finite right side, and no variable outside
$x_1,\ldots,x_n$. For each symbol and action there is at most one
rule. The relevant labelled transition system is his action-based
$\mathcal L^{\mathsf a}_{\mathcal G}$, which is deterministic here.
All initial terms and all configurations reached in finitely many
steps are finite ground terms. They are therefore regular syntactic
terms in the sense required by his theorem. Unused arguments are
permitted: the remark on shortest sink words in his §2 explicitly
states that the proof needs no normalization making every argument
reachable.

Write $\sim_k$ for his $k$-round bisimulation approximants, with
$\sim_0$ universal, and
$\operatorname{el}(S,T)=\max\{k:S\sim_kT\}$, taking value $\omega$
for bisimilar terms. In this grammar, for every $k\ge0$,

$$
S_A\sim_kS_B
\quad\Longleftrightarrow\quad
\forall |p|<k\quad r_{A(\mathbf K)}(p)=r_{B(\mathbf K)}(p).
\tag{SPC.26}
$$

For $k=0$ both conditions are vacuous. At the next round the enabled
actions distinguish the three reached labels. At equal branches their
unique child transitions require the previous-round conditions on both
children. At equal leaves the same observation marker reaches the same
dead sink, while all native descendants are absent. This proves (SPC.26)
by induction. A first discrepancy cannot be an absent/reached pair
without an earlier ancestor discrepancy. Hence a first native mismatch
at depth $d$ gives $\operatorname{el}(S_A,S_B)=d$, not $d+1$.
Inclusive agreement through $h$ is $S_A\sim_{h+1}S_B$.
Jančar's special convention for open variable terms is irrelevant:
these configurations are ground.

For completeness, let $n=\operatorname{Size}(S_A,S_B)$ be the number
of nodes in their joint least syntactic graph presentation, allowing
shared subterms. [Jančar, §3, Theorem 7][FOG] gives grammar-dependent
computable numbers $c,\mathcal E$ such that

$$
S_A\not\sim S_B\quad\Longrightarrow\quad
\operatorname{el}(S_A,S_B)
 \le c\bigl(\mathcal E n+n^2\bigr).
\tag{SPC.27}
$$

His term “small” for $c$ explicitly includes computability from the
grammar; $\mathcal E$ is also computable. Thus one may take the integer
ceiling of the right side for $H$. Any computable upper bound on $n$,
such as the total size of the two finite syntax trees, also suffices.
Agreement through inclusive $H$ forces equality, since it gives
$\operatorname{el}\ge H+1$. Otherwise the finite prefix evaluator finds
a discrepancy at depth at most $H$. Equivalently, [Corollary 8][FOG]
decides bisimilarity directly, and the correspondence above transfers
its answer to native equality. Neither computation presupposes
rationality of the native output. $\square$

**Corollary 7.3 (all retained closed positive equations and filters).**
For Definition 7.1, consistency of the defining subsystem together with
all the additional positive equations and fixed image filters is
decidable. If consistent, it has exactly the valuation $\mathbf K$.

Proof. Every solution of the conjunction must first solve (SPC.21),
so must equal $\mathbf K$. Apply Theorem 7.2 to each additional
$A_l(\mathbf K)=B_l(\mathbf K)$ and conjoin the answers. A second
definition for the same head is therefore checked as an equality,
not interpreted as another possible production. A failed comparison
rejects this valuation; it does not authorize choosing independent
values for its repeated state occurrences.

Image tests remain separate conjuncts. Their decision here is an exact
application of [NIS, Definition 3.1 and Proposition 4.3][NIS], with the
following full correspondence. Its parameter tuple is empty: all grounds,
atomic indices and powers are already fixed. There is exactly one
defining equation per state, every state is defined, every recursive
right side is explicitly pair-rooted, and the only other constructors
are its permitted finite grounds, $\Omega$ and fixed native decorators.
There are no free states and therefore one empty saturation mode;
its canonical guarded extension is precisely $\mathbf K$. Each
retained filter is literally an expression $C_l\in L_{s_l}$ of that
definition, with a supplied finite threshold. Additional equations
do not change this extension and are checked separately.
Proposition 4.3's Presburger guard in an empty parameter tuple is a
decidable truth value for the conjunction of these exact filters.
This uses its closed functional canonical case only; no replacement
of arbitrary shared unknowns by $\Omega$ or additional model-checking
theorem is assumed.

In particular, selecting a guarded subsystem from a larger equation
list is valid for this consumer only when every variable is covered.
An uncovered residual is still an existential tree variable, outside
this corollary. The existence of some syntactic selection is a finite
check on a supplied list; its existence for every acquired-input chart
has not been proved. The bound (SPC.27) concerns fixed expressions and
fixed numeric data, not elimination of unbounded rank parameters or a
uniform depth bound for arbitrary acquired inputs. $\square$

## 8. Original-address finite-state representation obstructions

**Definition 8.1 (the supplied right-spine instance).** Specialize
Definition 3.1 to

$$
F(y)=\langle\alpha,\rho y\rangle,\qquad
U(x,y)=\langle x,\langle y,F(y)\rangle\rangle.
\tag{SPC.28}
$$

The old cut is $P=\{\varepsilon\}$, with its entire one-reached-hole
row. The literal history is exactly

$$
H_0=\{(0,\varepsilon,\mathsf{branch}),
       (0,R,\mathsf{branch}),(0,RR,\mathsf{branch}),
       (0,RRL,\alpha)\},
\tag{SPC.29}
$$

and the signed history is exactly

$$
H_{\rm rel}=\{(1,RL,0,RRR,=),\ (0,RL,0,RR,\ne)\}.
\tag{SPC.30}
$$

Retain $Q=\{L,RL,RR\}$ and certified final epoch $N=1$.
Theorems 3.2–3.3 apply with the hole at $R$, not $L$:
the entire fiber is all $U(x,y)$ with finite $x,y$, and its exact
three complete target rows have the common numbered-hole exterior
$\langle\square_1,\langle\square_2,\square_3\rangle\rangle$,
reached set $Q$, and partitions

$$
r_0:\{\{1,2\},\{3\}\},\qquad
r_1:\{\{1,3\},\{2\}\},\qquad
r_2:\{\{1\},\{2\},\{3\}\}.
\tag{SPC.31}
$$

Take $B=\{r_0,r_1\}$. Its exact strata remain
$D_0=\{U(y,y):y\in\mathcal T\}$ and
$D_1=\{U(F(y),y):y\in\mathcal T\}$; $r_2$ is retained in the
whole fiber. The positive record identifies the original $RRR$
subtree with $\rho y$, since the epoch-one $RL$ subtree is $\rho y$.
All its endpoints and both endpoints of the negative are reached.
The finite inequality $y\ne F(y)$ is the leaf-count inequality
(SPC.16). Thus this instance uses the entire supplied source family,
not unconstrained names for infinite trees.

Let $y_n=F^n(\beta)$. The actual finite witnesses from (SPC.18) are
$U(y_n,y_n)$ and $U(y_{n+1},y_n)$, retaining every literal, sign and
complete row, with discrepancy depth at least $n+1$. Taking $n=h+1$
suffices for every inclusive $h$. Under ARH Assumption 1.3 they are
alternative originals for the one source-total paid producer of
Theorem 3.2. This remains a supplied acquisition and complete-state
factoring premise, not a measurement of actual acquisition or cost.

Theorem 4.2 identifies their common contact set as the singleton
$\{W\}$, where

$$
K=\langle\alpha,\rho K\rangle,\qquad
W=\langle K,\langle K,K\rangle\rangle.
\tag{SPC.32}
$$

For comparison, Theorem 7.2 represents this same non-rational $K$
by the finite binary-state rules

$$
G(a,b)\xrightarrow{L}a,\qquad
G(a,b)\xrightarrow{R}G(b,\mathsf P(b,a)),
\quad\text{initial term }G(\mathsf a,\mathsf b).
\tag{SPC.33}
$$

After $j$ right actions the configuration is
$G(P_j(\mathsf a,\mathsf b),P_{j+1}(\mathsf a,\mathsf b))$.
Consequently, in original coordinates,

$$
K|_{R^j}=\rho^jK,\qquad K|_{R^jL}=T_j,\qquad
W|_{LR^jL}=T_j\qquad(j\ge0).
\tag{SPC.34}
$$

The first two equations also follow directly by distributing
$\rho^j$ through (SPC.32): its right child becomes $\rho^{j+1}K$
and its left child becomes $\rho^j\alpha$. In particular the side
index is $j$, while its address in $W$ has length $j+2$.
The grammar's finite syntax and finite initial term do not make its
unbounded sequence of configurations, or its expanded native output,
a finite native subtree graph.

**Theorem 8.2 (no nonempty sound ordinary parity contact output).**
Pad every native completion by its absent replies to obtain a full
binary tree over
$\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$ at the original
addresses. No ordinary nondeterministic finite-state parity tree
automaton has a nonempty accepted language contained in the padded
contact set of Definition 8.1.

More quantitatively, if a valid native tree $V$ is generated by a
rooted deterministic labelled graph with at most $q\ge1$ reachable
vertices, then

$$
V\not\equiv_{\,2q+2}W.
\tag{SPC.35}
$$

The same bound holds when “at most $q$ vertices” is replaced by “at
most $q$ distinct native whole subtrees”. A nonempty $q$-state parity
language consisting of valid native padded trees cannot be contained
even in the cylinder of agreement with $W$ through depth $2q+2$.

Proof. First fix the regular-witness implication used here. For an
ordinary top-down parity automaton, a transition chooses a node label
and two successor states. Its nonemptiness game has existential
vertices at states and universal vertices at the chosen transitions;
the universal player chooses the child. An accepted labelled tree and
its run give a winning strategy by following that run at the address
specified by the successive child choices. The game is finite and
has finitely many priorities; a state with no legal transition leads
to a losing odd sink. Give each transition vertex the priority
of its preceding state so that inserting these vertices does not
change the parity condition.

[Le Roux, §3, Theorem 3][PARITY] supplies a positional winning
strategy, using the convention that the largest priority seen
infinitely often is even. The other usual parity convention is
equivalent by renumbering priorities. The positional strategy chooses
one fixed label and pair of successors for every reached state.
Unfolding these choices gives an accepted padded tree with at most
$q$ distinct rooted padded subtrees. If the accepted language is
contained in valid padded native trees, this witness is valid, and
its reached native subtree values number at most $q$. This verifies
the regular-witness property at the precise output encoding in use.

Definition 8.1 and Theorem 4.2 give the contact set $\{W\}$ and its
non-rationality. Any nonempty sound accepted language would therefore
contain $W$ and, by the preceding implication, an accepted rational
native tree equal to $W$, a contradiction. This argument needs only
a nonempty sound subset, rather than an exact enumeration of contacts.

For the explicit prefix bound, ABC's supplied atomic recurrence and
index injectivity give distinct $T_0,\ldots,T_q$. Their heights obey
$\operatorname{ht}(T_0)=\operatorname{ht}(T_1)=0$ and
$\operatorname{ht}(T_j)=j-1$ for $j\ge1$, directly by
$T_{j+2}=\langle T_{j+1},T_j\rangle$ and the height of a pair.
Thus $\operatorname{ht}(T_j)\le j$. If $V\equiv_{2q+2}W$, every
subtree in (SPC.34) for $0\le j\le q$ is visible in full, since

$$
|LR^jL|+\operatorname{ht}(T_j)
\le (j+2)+j\le2q+2.
\tag{SPC.36}
$$

Matching the displayed leaves makes the entire subtree exactly $T_j$:
validity forbids additional reached descendants below those leaves.
So $V$ contains at least $q+1$ different native whole subtrees.
This proves (SPC.35). A graph with $q$ reachable vertices has at most
$q$ such values. The regular witness above then proves the cylinder
claim for a $q$-state parity language. This is an inclusive-depth
bound for a representation class, not a depth excluding $J_B$:
the actual finite witnesses exist at every depth. $\square$

**Theorem 8.3 (raw support and regular auxiliary-track boundary).**
Use finite partial native trees
$p::=\#\mid\alpha\mid\beta\mid\langle p,p\rangle$.
Each $\#$ is an independent unfinished frontier position.
Write $p\preceq u$ when every displayed native node agrees with $u$;
a displayed leaf also fixes absence at its strict descendants. Put

$$
\mathcal S_B=
\{p:\exists(u_r)_{r\in B}\in\prod_{r\in B}D_r
                   \quad\forall r\in B\ p\preceq u_r\}.
\tag{SPC.37}
$$

For the entire signed instance of Definition 8.1, $\mathcal S_B$
is not a regular finite ranked-tree language. In particular no exact
certificate language regular in a canonical padded convolution of
finitely many finite-tree tracks can have $\mathcal S_B$ as its
projection onto the unaltered partial-prefix track.

Proof. The language is downward closed under replacing displayed
subtrees by $\#$, because the same simultaneous whole sources still
witness membership. Membership at any supplied $p$ uses the already
supplied NSF finite observation decision: impose its displayed nodes
on one original per row and keep that original's entire $D_r$.
This reuse asserts neither regularity nor a new finite-feasibility
theorem.

Suppose a complete deterministic bottom-up automaton recognizes
$\mathcal S_B$. Determinization permits this assumption for any
ordinary regular finite-tree presentation. Let $p_n(W)$ retain the
native nodes of $W$ through inclusive depth $n$, putting $\#$ at
the next reached frontier. Because $W$ is a common closure point,
every $p_n(W)$ belongs to $\mathcal S_B$.

Run the automaton on these accepted finite trees. For every reached
address $v$ of $W$, its bottom-up state is defined for all sufficiently
large $n$. Enumerate those countably many addresses and successively
take infinite subsequences on which their states are constant.
A diagonal subsequence yields states $q(v)$, with an accepting
$q(\varepsilon)$ and with the native transition identities at every
branch and leaf of $W$. For each state that occurs, there is a finite
partial-tree representative $t_q$ having that state: take the subtree
at a suitable occurrence in a sufficiently late $p_n(W)$.

For each occurring state choose one native-labelled transition
witnessed at one of its occurrences in $W$. These choices define a
finite graph: its vertex $q$ has that label, and, at a branch, the
two chosen child states. Its unfolding $V$ from $q(\varepsilon)$
is a valid rational native tree with no $\#$ labels. For any finite
truncation of $V$, fill its unfinished frontier positions by the
representatives $t_q$ of their intended states. The resulting finite
partial tree has accepting root state, so is in $\mathcal S_B$.
Downward closure, replacing these fillers by $\#$ again, puts the
truncation itself in $\mathcal S_B$.

Every prefix of $V$ therefore has simultaneous actual witnesses in
all the exact row fibers. Hence
$V\in\overline{D_0}\cap\overline{D_1}=\{W\}$. This contradicts
the supplied non-rationality of $W$. The argument uses the exact
downward-closed support; it does not assume that accepted partial
trees satisfy their signs at an infinite limit.

Finally, projection of a regular finite-tree language through a
linear, possibly erasing tree homomorphism is regular. Forgetting
finitely many auxiliary coordinates in canonical convolution, and
pruning padding below a nullary symbol of the prefix track, is
such a projection. Thus an exact regular certificate language with
that projection would make $\mathcal S_B$ regular, a contradiction.
Finite auxiliary regular tracks can encode local annotations and
bounded certificates; they cannot give this exact raw support
projection. On infinite padded contact outputs their ordinary
existential parity projection is likewise a parity language, so
Theorem 8.2 also excludes a nonempty sound contact-output projection.

The claims require these regular projections onto original addresses.
They exclude neither nonregular decoders, richer encodings, global
constraint automata nor interpreted parameter grammars such as
(SPC.33). They also make no claim against a decision procedure whose
output is a truth value and finite witnesses at requested depths,
without a finite-state contact output. $\square$

## 9. Separate owned lifts above one original prefix

**Definition 9.1 (a bare-shift entire input and refinement).** Put
$V(x,y,z)=\langle x,\langle y,z\rangle\rangle$.
Take $P=\{\varepsilon\}$ with its complete one-hole old row,
$Q=\{L,RL,RR\}$, $N=1$, and exactly

$$
\begin{aligned}
H_0&=\{(0,\varepsilon,\mathsf{branch}),(0,R,\mathsf{branch})\},\\
H_{\rm rel}
 &=\{(1,L,0,RR,=),\ (0,L,0,RR,\ne)\}.
\end{aligned}
\tag{SPC.38}
$$

This is the bare shift $z=\rho x$, rather than the proper-context
map $F$ of Definition 8.1.

For a general complete acquired input and finite set $B$ of at least
two distinct attained whole rows, retain the exact finite fibers $D_r$
and write

$$
J_B(h)\iff
\exists(u_r)_{r\in B}\in\prod_{r\in B}D_r
              \quad\forall r,s\in B\ u_r\equiv_hu_s.
\tag{SPC.39}
$$

A compact Hausdorff refinement consists of a compact Hausdorff space
$Z$, a map $j:\mathcal T\to Z$, and a continuous
$\pi:Z\to\widehat{\mathcal T}$ with $\pi(j(u))=u$.
For each row take the closure of its entire jointly constrained
realizations,
$C_r=\overline{j(D_r)}^{\,Z}$.

**Theorem 9.2 (exact owned-lift condition and strict native separation).**
For every such refinement,

$$
\begin{aligned}
\forall h\ J_B(h)
&\quad\Longleftrightarrow\quad
 \bigcap_{r\in B}\pi(C_r)\ne\varnothing\\
&\quad\Longleftrightarrow\quad
 \exists W\ \exists(\xi_r)_{r\in B}\in\prod_{r\in B}C_r
       \quad\forall r\in B\ \pi(\xi_r)=W.
\end{aligned}
\tag{SPC.40}
$$

The lifts $\xi_r$ are separate row-specific points. They cannot in
general be required to coincide: the entire input (SPC.38) admits
two attained complete rows with all-depth actual finite witnesses
and a regular finite-valued source refinement for which
$C_0\cap C_1=\varnothing$ although
$\pi(C_0)\cap\pi(C_1)\ne\varnothing$.

Proof. The valid four-reply completion is a closed subset of the
product of a finite discrete alphabet over all finite addresses.
Validity is imposed by the root condition and the local conditions
on children of branches, leaves and absent nodes. It is compact
Hausdorff, with clopen inclusive-prefix cylinders.
For each $h$, the union of the depth-$h$ cylinders realized by every
$D_r$ is a finite union of clopen cylinders. These sets are nested
and are nonempty exactly when $J_B(h)$ holds. Compactness therefore
gives

$$
\forall h\ J_B(h)
\quad\Longleftrightarrow\quad
\bigcap_{r\in B}\overline{D_r}^{\,\widehat{\mathcal T}}
 \ne\varnothing.
\tag{SPC.41}
$$

Conversely a point in that intersection supplies, at each requested
$h$, one finite source from each exact row in its cylinder.
There are finitely many rows, so these choices form the required
simultaneous tuple.

The standard compact-image identity is

$$
\pi\!\left(\overline{j(D_r)}^{\,Z}\right)
       =\overline{D_r}^{\,\widehat{\mathcal T}}.
\tag{SPC.42}
$$

Continuity proves inclusion into the right side; compactness of
$C_r$ and the Hausdorff target make its image closed and containing
$D_r$, proving the reverse inclusion. This is reuse of compact-image
topology, not a new compactness theorem. Equations (SPC.41)–(SPC.42)
prove (SPC.40), with one preimage chosen separately for each row.
A finite common $W$ is impossible for distinct rows: the cylinder
displaying every leaf of a finite tree isolates that same finite
source, whose complete target row is unique.

For the strict source-faithful instance, use the already supplied
right clock

$$
c(\alpha)=0,\quad c(\beta)=1,\quad
c(\langle s,t\rangle)=2+c(t),\qquad
c(\rho^k t)=c(t)+k.
\tag{SPC.43}
$$

The last identity is [DelayedOriginalReadout,
right_clock_iterate][CLOCK], also supplied as
[NativePrefixIdentityReflection, kappa_iterate][KAPPA].
Let $\chi(t)=c(t)\bmod2$. Its quotient has
$\chi(\langle s,t\rangle)=\chi(t)$ and
$\chi(\rho t)=1-\chi(t)$; in particular $t\ne\rho t$
for every finite native $t$. No clock identity or its private
one-step helper is reproved here.

The two branch literals in (SPC.38) give exactly
$u=V(x,y,z)$ with all three original holes reached. The epoch-one
subtree at $L$ is $\rho x$, because the original root branch survives.
Thus its positive record gives $z=\rho x$. Its negative record is
$x\ne z$, which holds for every finite $x$ by (SPC.43), with both
original endpoints reached. Conversely every $V(x,y,\rho x)$
satisfies the entire old row, both literals and both guarded records.
Hence the whole original fiber is exactly

$$
D=\{V(x,y,\rho x):x,y\in\mathcal T\}.
\tag{SPC.44}
$$

The complete $Q$-exterior is
$V(\square_1,\square_2,\square_3)$, with every hole reached.
Because $x\ne\rho x$, the two selected whole rows and their exact
fibers are

$$
\begin{aligned}
r_0&:\{\{1,2\},\{3\}\},&
D_0&=\{V(t,t,\rho t):t\in\mathcal T\},\\
r_1&:\{\{1\},\{2,3\}\},&
D_1&=\{V(t,\rho t,\rho t):t\in\mathcal T\}.
\end{aligned}
\tag{SPC.45}
$$

Both are attained. The remaining possible partition is all singleton
classes, attained for example by
$x=\alpha,y=\langle\alpha,\alpha\rangle,z=\beta$.
It remains in $D$; no row or exterior has been discarded.
ARH Proposition 2.1 supplies one source-total paid producer for these
fixed public records, on the same original register through epoch one,
conditional on its complete accessible-state cut. Each displayed
source produces that same retained input. The traversal and comparison
costs are sourcewise finite, with no claimed uniform bound. The common
producer and cut remain premises and supply no extra clock port.

Given an inclusive depth $h$, choose the actual finite trees

$$
t_h=T_{2h+2},\qquad
u_h^0=V(t_h,t_h,\rho t_h),\qquad
u_h^1=V(t_h,\rho t_h,\rho t_h).
\tag{SPC.46}
$$

By [NLC, Lemma 3.1][NLC], both $t_h$ and
$\rho t_h=T_{2h+3}$ have minimum leaf depth $h+1$.
Every reply of both whole originals through depth $h$ is therefore
branch. They lie in the two exact fibers (SPC.45), so satisfy every
retained sign, guard and whole partition at that finite depth.
As $h$ increases both converge in original prefixes to the all-branch
tree $\Omega$.

Define the additional finite source predicate

$$
E(u)=
\begin{cases}
1,&u=V(x,y,z)\text{ and }\chi(x)=\chi(y),\\
0,&\text{otherwise}.
\end{cases}
\tag{SPC.47}
$$

It is an ordinary regular finite-tree test. A bottom-up state can
store the rightmost-leaf bit $\chi$, whether its root is a branch,
and, at a branch, the bit of its left child. At the root these
finitely many data decide whether the right child is a branch and
whether the bits of $x$ and $y$ agree. Thus $E$ does not depend
on an unverified automata recognition theorem for native histories.
It equals $1$ throughout $D_0$ and $0$ throughout $D_1$, since
$\chi(\rho t)=1-\chi(t)$.

Now let

$$
Z=\overline{\{(u,E(u)):u\in\mathcal T\}}
          ^{\,\widehat{\mathcal T}\times\{0,1\}},
\qquad j(u)=(u,E(u)),\qquad \pi(w,e)=w.
\tag{SPC.48}
$$

This is a compact Hausdorff refinement. The two row closures are
contained respectively in the disjoint closed color slices $e=1$
and $e=0$. Thus $C_0\cap C_1=\varnothing$.
The finite sequences (SPC.46) converge after lifting to
$(\Omega,1)\in C_0$ and $(\Omega,0)\in C_1$, respectively.
Both project to $\Omega$. Therefore

$$
\pi(C_0\cap C_1)=\varnothing
\quad\text{but}\quad
\Omega\in\pi(C_0)\cap\pi(C_1).
\tag{SPC.49}
$$

The predicate $E$ is an auxiliary mathematical refinement, not an
additional observed field in the acquired input (SPC.38). If such a
field were accessible at the cut it would change that input's fiber.
Here its two limiting values distinguish alternative originals.
Within each original all occurrences of $x$, its update $\rho x$,
its row equalities and the entire signed list still share their
one source. The separation therefore refutes cross-alternative
identification of refined points, not same-source sharing.
In particular $\rho\Omega=\Omega$ does not invalidate the finite
negative in (SPC.38); that negative was checked on (SPC.46), not
at the contact. $\square$

## 10. Transfer conditions and the remaining joint support problem

**Open problem 10.1 (unrestricted finite signed support).** For every
complete acquired input $I=(P,R,H_0,H_{\rm rel},Q,N)$ and every supplied
finite set $B$ of at least two distinct attained whole rows, decide
between a finite $H$ with $\neg J_B(H)$ and actual simultaneous finite
realizations for every requested depth. The whole old row, concrete exterior, reached
holes, complete partitions, all actual-epoch records and off-task
constraints remain imposed. This is the unchanged unrestricted
obligation, not a restriction to closed systems, rational contacts
or two rows.

Theorem 7.2 supplies exact comparison after a closed native valuation
has been faithfully presented. Corollary 7.3 checks every additional
positive equation on that one valuation and retains fixed image
filters at their explicit NIS scope. Neither result synthesizes
assignments to existential shared residuals, eliminates unbounded
correlated ranks, or proves that arbitrary exact row-fiber contacts
admit these presentations.

Theorem 8.2 excludes ordinary finite-state original-address contact
outputs even when only a nonempty sound subset is requested.
Theorem 8.3 gives the corresponding obstruction to exact downward-closed
raw prefix certificates with regular projections. These obstructions
favor retaining stronger symbolic descriptions, including carried
parameters, instead of requiring a finite native subtree graph.
They do not exclude a terminating algorithm that never outputs
a contact.

Equation (SPC.40) fixes how such descriptions may be combined: keep
each source's whole joint constraint relation and its own refined lift,
and identify only the common original-prefix projection across rows.
The next missing theorem is a completeness or density/lifting theorem
for arbitrary finite signed witnesses, preserving multiple positive
definitions, repeated values, images, ranks and all reached guards
simultaneously. Closure of the actual jointly constrained finite
realizations cannot be replaced by an intersection of separate
conjunct closures, a product of marginal source states, or the set
of completed positive solutions without that theorem. Finite
disequalities can escape to increasing addresses and are evaluated
on the finite witnesses only.

Once a justified all-depth conclusion is available, the existing NSF
supplied-depth procedure extracts the requested finite tuple. Merely
running it at successive depths, enumerating closed grammars without
a completeness theorem, or invoking compactness does not decide the
unrestricted alternative. Actual paid acquisition, complete accessible
state factoring and all action/resource quantities of Definition 5.3
remain separate supplied premises and obligations.

**Definition 10.2 (source and increment attribution).** The following
correspondences distinguish reused results from the deductions here.

| Source | Exact use and limit |
| --- | --- |
| Theorems 3.2–3.3 and 4.2 of this volume | Entire shifted-context source family, finite signed witnesses, singleton non-rational contact and its side ladder. Section 8 adds the parity-output and quantitative prefix obstruction, and the raw-support projection consequence; it does not claim a new contact family. |
| [Jančar, §2, rule (3); §3, Theorem 7 and Corollary 8][FOG] | Literature-attested equivalence and computable equivalence-level bound for first-order grammars. Section 7 supplies the native two-leaf-image correspondence, exact absence semantics and closed conjunctive equation consumer. Regular syntactic configurations and non-rational generated native trees are distinct. |
| [Le Roux, §3, Theorem 3][PARITY] | Literature-attested positional parity determinacy, used in the finite nonemptiness game to obtain a regular accepted output. The new native consequence uses the entire SPC signed family and its exact original-address encoding. |
| [NIS, Definitions 3.1 and 4.1, Proposition 4.3][NIS] | Image filters only for the explicitly closed, fixed-data, empty-free-state canonical extension in Corollary 7.3. No general free-state saturation or arbitrary multiple-definition solver is transferred. |
| [NSF, Theorem 4.3, Lemma 5.1 and Theorem 5.2][NSF] | Finite native existential queries, original-source reconstruction and supplied-depth witnesses are reused. Witness templates are not an all-solution contact presentation. |
| [NativeDepthPatterns, depthEquiv][DEPTH]; [NativeCutFibers, rowFiberEquiv][FIBERS] | Existing exact prefix/frontier and whole-row correspondences underpin the reused NSF source compilation. Their private inverse helpers remain part of those suppliers, not new proofs here. |
| [DelayedOriginalReadout, right_clock_iterate][CLOCK]; [NativePrefixIdentityReflection, kappa_iterate][KAPPA]; [NLC, Lemma 3.1][NLC] | Existing clock transport, its parity quotient, and atomic minimum depth supply the bare-shift counterexample's finite signs and witnesses. The increment is its entire acquired-input mapping and the strict separation of refined row lifts above one projected contact. |
| Compact-image topology | The closed-image identity in (SPC.42) is standard reuse. It yields no effective presentation of $C_r$ and no decision of projected intersections. |

The operation correspondence, representation obstructions and
source-faithful gluing constraint are repo-derived deductions using
these suppliers. They are ordinary mathematical arguments, without
an external-priority, undecidability, physical-realization or
kernel-verification assertion. Finite syntax supplies no absolute
atomic minimality or physical spacetime/dimension conclusion.

[FOG]: https://arxiv.org/html/1812.03518v2
[PARITY]: https://arxiv.org/html/1803.00655v2
[NIS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_SATURATION.md
[CLOCK]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[KAPPA]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.lean
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[FIBERS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean

## 追加锚（本行以下为增补区）

## 11. Pairwise persistence with least triple failure at depth three

**Definition 11.1 (one entire acquired four-hole input).** In the native
algebra of Definition 1.1 put

$$
\begin{aligned}
F(y)&=\langle\alpha,\rho y\rangle,\\
G(y)&=\langle\alpha,\rho^2y\rangle,\\
U_*(x,y)&=\langle x,\langle y,\langle F(y),G(y)\rangle\rangle\rangle.
\end{aligned}
\tag{SPC.11.1}
$$

Here $F$ is the proper-context map of Definition 8.1, and $G$ has
the same context with shift two. All occurrences of $y$ within
one source denote that same whole native value.

Take $P=\{\varepsilon\}$ with its complete one-hole old row,
authentic final epoch $N=2$, and the target cut

$$
Q=\{L,RL,RRL,RRR\},
\tag{SPC.11.2}
$$

numbered in that order. Retain exactly

$$
\begin{aligned}
H_0=\{&(0,\varepsilon,\mathsf{branch}),
       (0,R,\mathsf{branch}),
       (0,RR,\mathsf{branch}),\\
      &(0,RRL,\mathsf{branch}),
       (0,RRR,\mathsf{branch}),\\
      &(0,RRLL,\alpha),(0,RRRL,\alpha)\},\\
H_{\rm rel}=\{&
 (1,RL,0,RRLR,=),\
 (2,RL,0,RRRR,=),\\
 &(0,RL,0,RRL,\ne),\
 (0,RL,0,RRR,\ne),\
 (0,RRL,0,RRR,\ne)\}.
\end{aligned}
\tag{SPC.11.3}
$$

There are no other constraints in this instance. The entire old
row, all listed literal and signed records, both reached guards
for every relation, and Definition 1.2's supplied paid-source
complete-state contract are retained. Epochs zero, one and two
refer to the same original register.

**Theorem 11.2 (entire fiber, exact reconstruction and every row).**
The input of Definition 11.1 has exactly the entire original fiber

$$
D_*=\{U_*(x,y):x,y\in\mathcal T\}.
\tag{SPC.11.4}
$$

Its complete target-row image consists of exactly four attained
labels. All have reached set $Q$ and the entire exterior

$$
\langle\square_1,
 \langle\square_2,\langle\square_3,\square_4\rangle\rangle\rangle.
\tag{SPC.11.5}
$$

Their partitions and entire strata are

$$
\begin{aligned}
r_0&:\{\{1,2\},\{3\},\{4\}\},&
D_0&=\{U_*(y,y):y\in\mathcal T\},\\
r_1&:\{\{1,3\},\{2\},\{4\}\},&
D_1&=\{U_*(F(y),y):y\in\mathcal T\},\\
r_2&:\{\{1,4\},\{2\},\{3\}\},&
D_2&=\{U_*(G(y),y):y\in\mathcal T\},\\
r_3&:\{\{1\},\{2\},\{3\},\{4\}\},&
D_3&=\{U_*(x,y):x,y\in\mathcal T,\
                    x\ne y,\ x\ne F(y),\ x\ne G(y)\}.
\end{aligned}
\tag{SPC.11.6}
$$

Every source in each right-hand set satisfies the complete original
input and its stated row. Conversely every source satisfying that
input and row is reconstructed as the same original source in that
set, with its original whole values.

Proof. The seven epoch-zero literals force precisely a decomposition

$$
u=\langle x,\langle y,
        \langle\langle\alpha,z\rangle,
               \langle\alpha,w\rangle\rangle\rangle\rangle
\tag{SPC.11.7}
$$

with $x,y,z,w\in\mathcal T$. To see the entire direction, the branch
literals at $\varepsilon,R,RR$ force the first three pairings.
Those at $RRL,RRR$ force their two child pairings, and the literals
at $RRLL,RRRL$ fix the displayed alpha leaves. Their other children
are exactly $z,w$, without any extra restrictions. These values
are the actual subtrees of the original $u$.

All the strict original ancestors of $RL$ are branches.
They survive every update, so

$$
(\rho u)|_{RL}=\rho y,\qquad
(\rho^2u)|_{RL}=\rho^2y.
\tag{SPC.11.8}
$$

The original addresses $RRLR,RRRR$ are reached by the displayed
branch skeleton. Thus the two positive records, including their
guards, force $z=\rho y$ and $w=\rho^2y$. The relation endpoint
values after this substitution are exactly:

| Retained record | First reached whole value | Second reached whole value |
| --- | --- | --- |
| $(1,RL,0,RRLR,=)$ | $\rho y$ | $\rho y$ |
| $(2,RL,0,RRRR,=)$ | $\rho^2y$ | $\rho^2y$ |
| $(0,RL,0,RRL,\ne)$ | $y$ | $F(y)$ |
| $(0,RL,0,RRR,\ne)$ | $y$ | $G(y)$ |
| $(0,RRL,0,RRR,\ne)$ | $F(y)$ | $G(y)$ |

Every listed original endpoint is reached in (SPC.11.7), and the
two nonzero-epoch endpoints remain reached by (SPC.11.8). Both
guards are therefore established for every record on the whole
displayed domain, before its sign is checked.

The proper-context leaf-count argument (SPC.16), applied to
$C[z]=\langle\alpha,z\rangle$ with shifts one and two, gives

$$
\ell(F(y))=1+\ell(\rho y)>\ell(y),\qquad
\ell(G(y))=1+\ell(\rho^2y)>\ell(y).
\tag{SPC.11.9}
$$

Thus the first two negatives hold for every finite $y$.
For the third, use the existing finite right clock (SPC.43):

$$
c(\rho y)=c(y)+1,\qquad c(\rho^2y)=c(y)+2.
$$

These whole values differ. Free ordered pairing then gives
$F(y)\ne G(y)$. The clock transport is the supplied
[DelayedOriginalReadout, right_clock_iterate][CLOCK], equivalently
[NativePrefixIdentityReflection, kappa_iterate][KAPPA];
no new clock law is required.

Consequently every $U_*(x,y)$ has the old root row, every literal
in (SPC.11.3), both positive records, and all three finite negatives
with their guards. Conversely (SPC.11.7)–(SPC.11.8) recover that
very original source as $U_*(x,y)$. This proves (SPC.11.4) in both
directions; no witness subset replaces its entire fiber.

All four target holes are reached. Their values are
$x,y,F(y),G(y)$, of which the last three are pairwise distinct.
The first value can equal exactly one of those three or none.
These are all and only the partitions in (SPC.11.6), with precisely
the displayed conditions. The first three rows are attained for
every finite $y$. For the all-singleton row take $x=\alpha,y=\beta$:
the last two values are branches and the second is beta, all
different from alpha. This proves attainment and exhausts the
complete row image, including its concrete exterior.

For actual acquisition the finite public schedule in
[ARH, Proposition 2.1][ARH] uses precisely the coordinates of
(SPC.11.3), the old root cut, and final epoch two. It acquires
the epoch-zero literals and endpoint descriptions, then the
epoch-one $RL$ description, then the epoch-two $RL$ description
on the same register. The two later descriptions are compared
with their previously acquired original counterparts before the
stipulated complete cut. Every source in (SPC.11.4) gives the
stated signs and replies, hence the same retained input under
ARH Assumption 1.3. The converse source correspondence is that
supplier's complete-state premise, instantiated with these
coordinates. Paid acquisition is sourcewise finite; this
argument supplies no uniform cost or free comparison port.
$\square$

**Theorem 11.3 (persistence of every selected pair).** For each
two-element $A\subseteq\{r_0,r_1,r_2\}$ and every $h\in\mathbb N$,

$$
J_A(h).
\tag{SPC.11.10}
$$

Here $J_A$ is (SPC.39) on the entire strata (SPC.11.6).
All witnesses are finite originals satisfying the entire input
of Definition 11.1.

Proof. For $r_0,r_1$, put $y_t=F^t(\beta)$.
The native prefix estimate (SPC.9), followed by the proper
context's one-edge guard, gives

$$
\delta(F(s),F(t))\ge\delta(s,t)+1.
$$

This is the guarded-prefix supplier used in Theorem 3.3 with
$C[z]=\langle\alpha,z\rangle$ and $a=1$.
Since $\delta(\beta,F(\beta))=0$, its iteration gives
$\delta(y_t,y_{t+1})\ge t$. The two sources

$$
U_*(y_t,y_t)\in D_0,\qquad
U_*(y_{t+1},y_t)\in D_1
\tag{SPC.11.11}
$$

share their entire right subtree. Their only differences occur
below the original $L$ hole, so their first discrepancy has depth
at least $t+1$. Taking $t=h+1$ proves $J_{\{r_0,r_1\}}(h)$.

For $r_0,r_2$, put $z_t=G^t(\beta)$.
The same supplier with shift two gives

$$
\delta(G(s),G(t))\ge\delta(s,t)+2,
\qquad
\delta(z_t,z_{t+1})\ge2t.
$$

The finite sources $U_*(z_t,z_t)\in D_0$ and
$U_*(z_{t+1},z_t)\in D_2$ again have an identical complete
right part. Their discrepancy depth is at least $1+2t$.
The choice $t=h+1$ proves $J_{\{r_0,r_2\}}(h)$.

For $r_1,r_2$, take $y=T_{2h+2}$, where $T_n=\rho^n\alpha$.
The existing atomic-depth formula [NLC, Lemma 3.1][NLC] gives

$$
\mu(\rho y)=\mu(T_{2h+3})=h+1,\qquad
\mu(\rho^2y)=\mu(T_{2h+4})=h+2.
\tag{SPC.11.12}
$$

Both trees therefore reply branch at every relative address of
length at most $h$, and so $\rho y\equiv_h\rho^2y$.
The sources

$$
U_*(F(y),y)\in D_1,\qquad
U_*(G(y),y)\in D_2
\tag{SPC.11.13}
$$

share their entire right subtree. Inside their left subtree they
share the alpha child; only the right children $\rho y,\rho^2y$
can differ. Those children are at original address $LR$, so the
sources agree at least through depth $h+2$, and hence through $h$.
Every membership assertion here is Theorem 11.2 on actual finite
whole values. In particular its three retained negatives continue
to hold for every iterate and every atomic choice; no negative
is inferred from a completed limit. $\square$

**Theorem 11.4 (least triple failure is exactly three).** For
$B=\{r_0,r_1,r_2\}$ in Definition 11.1,

$$
J_B(2),\qquad \neg J_B(3).
\tag{SPC.11.14}
$$

Consequently the least inclusive failed depth is $H=3$.

Proof. To witness depth two, set
$y=\langle\alpha,\langle\alpha,\alpha\rangle\rangle$ and take

$$
\bigl(U_*(y,y),\ U_*(F(y),y),\ U_*(G(y),y)\bigr)
 \in D_0\times D_1\times D_2.
\tag{SPC.11.15}
$$

Theorem 11.2 checks their entire retained histories and exact
partitions. Their complete original reply tables through depth
two are identical:

| Original address | Common reply |
| --- | --- |
| $\varepsilon$ | $\mathsf{branch}$ |
| $L$ | $\mathsf{branch}$ |
| $R$ | $\mathsf{branch}$ |
| $LL$ | $\alpha$ |
| $LR$ | $\mathsf{branch}$ |
| $RL$ | $\mathsf{branch}$ |
| $RR$ | $\mathsf{branch}$ |

For $LR$, the first source has the right child of $y$, a branch;
the other two have $\rho y$ and $\rho^2y$, branches because $y$
is a branch. The other six replies follow from the displayed
skeleton and fixed alpha children. These seven addresses are
all words of length at most two. Thus (SPC.11.15) is an actual
simultaneous witness of $J_B(2)$.

For the negative assertion, suppose an arbitrary tuple in the
entire product agreed through depth three. By the converse
direction of Theorem 11.2 it has the form

$$
u_0=U_*(y_0,y_0),\qquad
u_1=U_*(F(y_1),y_1),\qquad
u_2=U_*(G(y_2),y_2)
\tag{SPC.11.16}
$$

for independent finite $y_0,y_1,y_2$. No equality between these
parameters is assumed.

The original $L$ and $LL$ replies of $u_1$ are respectively
branch and alpha. Agreement forces $y_0$ to be a branch with
left child alpha, because the entire $L$ subtree of $u_0$ is
$y_0$. Hence the $RL$ and $RLL$ replies of $u_0$ are branch
and alpha. Agreement at those two original addresses now forces
$y_1,y_2$ to be branches, each with left child alpha.
Write $y_i=\langle\alpha,b_i\rangle$ for $i=1,2$.

The address $LRL$ is reached in both $u_1,u_2$: their $L$
subtrees are branches, and their $LR$ subtrees are respectively
$\rho y_1,\rho^2y_2$, also branches. Native distribution and
the two alpha updates give

$$
\begin{aligned}
u_1|_{LRL}&=\rho\alpha=\beta,
&
r_{u_1}(LRL)&=\beta,\\
u_2|_{LRL}&=\rho^2\alpha=\langle\beta,\alpha\rangle,
&
r_{u_2}(LRL)&=\mathsf{branch}.
\end{aligned}
\tag{SPC.11.17}
$$

These different replies occur at an original address of length
three, contradicting the assumed agreement. All subtree uses
in this contradiction have their required branch ancestors;
absence is never treated as a reached negative or omitted from
the prefix table. The argument applies to every tuple
(SPC.11.16), so $J_B(3)$ fails on the entire product.

Inclusive-prefix agreement is monotone downward in depth.
The depth-two witness therefore supplies depths zero and one.
Failure at three excludes every greater depth. This proves
the claimed least $H$. $\square$

## 12. The obstruction to a pairwise replacement

**Corollary 12.1 (pairwise contacts do not imply a multiway contact).**
Let $C_i=\overline{D_i}^{\,\widehat{\mathcal T}}$, for $i=0,1,2$,
where $\widehat{\mathcal T}$ is the original four-reply completion
of Definition 4.1. For the entire strata of Definition 11.1,

$$
C_i\cap C_j\ne\varnothing\quad(i\ne j),\qquad
C_0\cap C_1\cap C_2=\varnothing.
\tag{SPC.12.1}
$$

Thus the criterion requiring all selected two-row subfamilies to
be persistent cannot replace the finite-family predicate (SPC.39).

Proof. The compact-cylinder equivalence (SPC.41), already supplied
in Theorem 9.2, applies to closures of entire finite row strata.
Theorem 11.3 gives its pairwise nonempty intersections. If there
were a point in the triple intersection, its inclusive depth-three
cylinder would meet every $D_i$. Choosing one finite original from
each intersection with that same cylinder would give $J_B(3)$,
contrary to Theorem 11.4. This proves the empty triple intersection.

Every one of the three pair predicates is true at every depth on
this fixed full native input, whereas the required triple predicate
already fails at depth three. Independently chosen pair tuples,
or separate pairwise contact points, therefore do not supply the
one simultaneous tuple required by (SPC.39). $\square$

**Definition 12.2 (supplier correspondence and unresolved scope).**
The whole old row and actual signed-epoch meanings remain
[ARH, Definitions 1.1–1.2 and Assumption 1.3][ARH]; its Proposition
2.1 supplies the paid producer correspondence for the fixed schedule.
[NIC, Theorems 3.2 and 4.3][NIC] already provide entire positive
and complete signed-row image covers. Theorem 11.2 gives both
original-source directions explicitly for this four-hole input;
it does not replace any source stratum by a sample.

The proper-context prefix growth in (SPC.9) and Theorem 3.3,
the right-clock transport (SPC.43), and
[NLC, Lemma 3.1][NLC] supply respectively the guarded pair
iterations, the finite third negative, and the atomic pair
witnesses. The new deduction is their full native four-row
reconstruction together with pairwise persistence and the
all-tuple least triple failure. Standard compactness is used
only as the intermediate equivalence (SPC.41).
No external-priority assertion is attached to this deduction.

[SLP, Lemma 2.1 and Theorem 3.1][SPC-SLP] lift whole signed
conjunctions at the fixed scalar and finite-residual data of
their normalized Cartesian scope; they do not identify
different alternative originals or turn separate pair
witnesses into a common triple. Its Open problem 7.1 and
Open problem 10.1 of this volume retain the unknown coupled
contact and finite-barrier obligations. Exact positive normalization
is already supplied by NIC; the remaining question is simultaneous
common original-prefix depth of the coupled whole source outputs,
including whether some finite barrier exists.

Theorem 11.4 is a finite native obstruction to a multiway
criterion, with an exact failed depth. It is not native
undecidability and does not decide Open problem 10.1 on
arbitrary inputs. In this same example the persistent pairs
still prevent any finite original prefix from determining
the entire target row, by (ARH.2.2); triple exclusion alone
does not assert such row recovery. All source parameters are
mathematical values, and actual acquisition and complete-state
factoring remain supplied premises.

[SPC-SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md

## 追加锚（本行以下为增补区）
## 13. A deterministic one-counter realization of the closed reply interface

**Definition 13.1 (normalized closed inputs and four replies).** Use the
closed defining subsystem of Definition 7.1, with every explicitly supplied
ground state definition inlined and every fixed native power distributed
through an explicit pair. A normalized expression has the finite syntax

$$
e ::= \alpha\mid\beta\mid\Omega\mid\langle e,e\rangle
       \mid \rho^aX_i,
\qquad a\in\mathbb N.
\tag{SPC.50}
$$

The right side of a defining equation is a pair of expressions (or a
finite ground after the permitted inlining), so its root is never a
positive-power state. Every state occurrence remains below an explicit
pair. States are nullary and repeated names denote one shared value. Outputs
may use the same syntax, exact finite constants and $\Omega$; an output
root need not itself be pair guarded. Negative, variable and
parameter-recursive powers are outside this definition. The zero-state case
is allowed.

Let $\Sigma=\{L,R\}$ and
$\mathcal R=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. For a
completed output $Z$, let $r_Z(p)$ be its exact reply at every original
address $p\in\Sigma^*$, including the root and every absent suffix. Put
$\mathcal L_\tau(Z)=\{p:r_Z(p)=\tau\}$. These are the same original-address
replies used by Definitions 1.1 and 7.1; normal-code depth and an
unlabelled reached-address trace are not substituted for them.

The native identities needed below are

$$
T_0=\alpha,\qquad T_1=\beta,\qquad
T_{n+2}=\langle T_{n+1},T_n\rangle,
\qquad T_n=\rho^n\alpha .
\tag{SPC.51}
$$

They follow from the leaf laws and distribution of $\rho$ through pairing.
Thus $\rho^c\beta=T_{c+1}$, while an explicit syntax pair preserves its
accumulated exponent when an original letter is consumed.

**Definition 13.2 (the finite one-counter machines).** A configuration is
$(q,c)$ with $c\in\mathbb N$. A transition tests $c=0$ or $c>0$, reads
$L$, $R$ or $\varepsilon$, and changes $c$ by $-1$, $0$ or $+1$; a decrement
is present only on a positive test. Give every explicit pair occurrence
$e=\langle e_L,e_R\rangle$ a control $P_e$, and use controls
$q_\alpha,q_\beta,O_\Omega$. For each occurrence $\rho^aX_i$, include
$J_{d,i}$ for $0\le d\le a$, sharing a control whenever $(d,i)$ is the
same. Add $A,V,B,H_\alpha,H_\beta,N$. The transition table is

| control | test | read | destination | update |
| --- | --- | --- | --- | --- |
| $P_{\langle e_L,e_R\rangle}$ | either | $L$ | $q_{e_L}$ | $0$ |
| $P_{\langle e_L,e_R\rangle}$ | either | $R$ | $q_{e_R}$ | $0$ |
| $O_\Omega$ | either | $L$ or $R$ | $O_\Omega$ | $0$ |
| $q_\alpha$ | either | $\varepsilon$ | $A$ | $0$ |
| $q_\beta$ | either | $\varepsilon$ | $A$ | $+1$ |
| $J_{d,i}$, $d>0$ | either | $\varepsilon$ | $J_{d-1,i}$ | $+1$ |
| $J_{0,i}$ | either | $\varepsilon$ | $q_{E_i}$ | $0$ |
| $A$ | $0$ | $\varepsilon$ | $H_\alpha$ | $0$ |
| $A$ | $>0$ | $\varepsilon$ | $V$ | $-1$ |
| $V$ | $0$ | $\varepsilon$ | $H_\beta$ | $0$ |
| $V$ | $>0$ | $\varepsilon$ | $B$ | $-1$ |
| $B$ | either | $L$ | $A$ | $+1$ |
| $B$ | either | $R$ | $A$ | $0$ |
| $H_\alpha,H_\beta$ | either | $L$ or $R$ | $N$ | $0$ |
| $N$ | either | $L$ or $R$ | $N$ | $0$ |

Here $q_{E_i}$ denotes the control for the normalized root
$\langle E_i,F_i\rangle$ of the defining right side, and $q_O$ is the
output-root control. The initial configuration is
$(q_O,0)$. Stable controls are all $P_e$, $O_\Omega$, $B$,
$H_\alpha,H_\beta,N$. The four accepting sets are

$$
F_\alpha=\{H_\alpha\},\quad F_\beta=\{H_\beta\},\quad
F_{\mathsf{branch}}=\{P_e:e\text{ is a pair occurrence}\}\cup\{O_\Omega,B\},
\quad F_{\mathsf{absent}}=\{N\}.
\tag{SPC.52}
$$

For each reply $\tau$, write $M_{O,\tau}$ for this common transition
system with initial state $(q_O,0)$ and accepting set $F_\tau$. Acceptance is
finite-word final-state acceptance at any nonnegative counter. Epsilon moves
consume no original address letter. Administrative controls are nonaccepting.

**Theorem 13.3 (determinism, lawful updates and finite administration).**
The machines of Definition 13.2 are classical deterministic one-counter
machines with epsilon moves. For each control, input letter and counter test
there is at most one transition; an epsilon rule excludes input rules at the
same control and test. All reachable counters are nonnegative. From the
initial configuration and after every consumed address letter, finite
administration reaches exactly one stable head, and every stable head has
both next-letter moves.

**Proof.** The normalized syntax and the finite set of fixed remainders give
finitely many controls. Every displayed update is a unit update. The only
negative updates have explicit positive tests, so induction from counter zero
proves nonnegativity. Pair and stable-head controls have only input rules;
all other controls have exactly one epsilon rule for each test and no input
rule. Shared $J_{d,i}$ controls therefore give one transition, not competing
ones.

At $J_{d,i}$, exactly $d$ increments reach $J_{0,i}$, whose zero-update
step enters the normalized defining root. Pair guardedness makes that root a
pair or a ground leaf, never another decorated-state root, so this chain
cannot form an epsilon cycle. A ground leaf enters $A$ and reaches a stable
head in at most two further tests. The $A$ and $V$ rules implement the two
lawful decrements in (SPC.51); no arbitrary threshold or hidden restoration
is present. A decorated occurrence with exponent $a$ uses at most $a+4$
epsilon steps, independently of the entering counter.

A pair and $O_\Omega$ are already stable. From $B$, an input enters $A$;
from a stable leaf, either input enters $N$; from an explicit pair an input
selects its child without changing the counter. Thus administration is finite
at the root and after every letter. Stable controls have no epsilon rules
and total $L,R$ moves, proving uniqueness of the terminal stable head. This
is a finite-chain termination statement, not a native-description size or
compact-input complexity bound. $\square$

**Theorem 13.4 (exact four-language correspondence).** For every normalized
closed input of Definition 13.1 and every output $O$,

$$
L(M_{O,\tau})=\mathcal L_\tau(\llbracket O\rrbracket)
\qquad(\tau\in\mathcal R).
\tag{SPC.53}
$$

Consequently the four languages partition $\Sigma^*$, including the empty
address, native leaf images and every absent suffix.

**Proof.** Interpret configurations by

$$
\begin{aligned}
(q_{e},c)&\longmapsto\rho^c\llbracket e\rrbracket,\qquad
(J_{d,i},c)\longmapsto\rho^{c+d}\llbracket X_i\rrbracket,\\
(A,c)&\longmapsto T_c,&(V,c)&\longmapsto T_{c+1},&(B,c)&\longmapsto T_{c+2},\\
(H_\alpha,c)&\longmapsto\alpha,&(H_\beta,c)&\longmapsto\beta,&
(O_\Omega,c)&\longmapsto\Omega.
\end{aligned}
\tag{SPC.54}
$$

$N$ denotes an absent position and every descendant. A $J$ increment preserves
$c+d$. At $J_{0,i}$ the defining equation identifies the interpreted state
with its normalized root. At $q_\alpha$ and $q_\beta$, (SPC.51) gives $T_c$
and $T_{c+1}$. At $A$, zero is $T_0$ and a positive counter decrements to
$V$ without changing the represented $T_c$; at $V$, zero is $T_1$ and a
positive counter decrements to $B$ while preserving $T_{c+1}$.

For an explicit pair, native distribution gives
$\rho^c\langle s,t\rangle=\langle\rho^cs,\rho^ct\rangle$, so its $L,R$
transitions select exactly the addressed child and keep $c$. From $(B,c)$,
(SPC.51) gives left subtree $T_{c+1}$ and right subtree $T_c$; the $L$ rule
enters $(A,c+1)$ and the $R$ rule enters $(A,c)$. From $O_\Omega$ both
children are $\Omega$. From either stable leaf both children are absent and
$N$ remains absent on every suffix.

Induct on address length. The initial finite administration reaches the
root's unique stable head with its exact reply. After a letter, the stable
transition selects the actual child or the absent convention, and the finite
administration preserves and classifies that child by (SPC.54). This proves
that the stable label after exactly $p$ is $r_{\llbracket O\rrbracket}(p)$,
including $p=\varepsilon$. Administrative controls never accept and stable
controls have no epsilon successors, so a run cannot accept by stopping in
the middle of administration. The four accepting sets therefore give
(SPC.53) and its partition. $\square$

**Theorem 13.5 (equality through the classical one-counter supplier).** For
two outputs $O,O'$ of Definition 13.1,

$$
\llbracket O\rrbracket=\llbracket O'\rrbracket
\Longleftrightarrow
\bigwedge_{\tau\in\mathcal R}
L(M_{O,\tau})=L(M_{O',\tau}).
\tag{SPC.55}
$$

The right side is decidable by the classical deterministic one-counter
language-equivalence result of Böhm, Göller and Jančar, *Equivalence of
Deterministic One-Counter Automata is NL-complete*, arXiv:1301.2181v1,
Theorem 3 and Appendix, PDF pp.23--24
([primary source](https://arxiv.org/pdf/1301.2181v1)). The Appendix's classical
interface is the one used here: finite controls and alphabet, transitions
with zero/positive tests and updates in $\{-1,0,1\}$, no decrement at zero,
unique transition per control/letter/test, epsilon/input exclusivity, initial
counter zero, and final-state acceptance at any nonnegative counter. Its
reduction may add an internal acceptance letter; that letter is not an
original address.

**Proof.** A completed ordered labelled tree is determined by its reply at
every finite address, so equality is equivalent to equality of its four
reply languages. Theorem 13.4 gives (SPC.55)'s machine languages. The
supplier's Appendix explicitly transfers decidability from its normalized
presentation to this classical final-state convention. Apply it separately
to the four finite machine pairs. No real-time-only, empty-counter-only or
unlabelled-trace convention is used, and the supplier's NL classification is
not transferred to a compact-input complexity claim for these native
expressions. $\square$


**Proposition 13.6 (diagnostics and the exact presentation boundary).** The
one-counter correspondence has the following concrete checks.

1. Pair traversal keeps the whole exponent: the $L$ subtree of
   $\rho^2\langle\alpha,\alpha\rangle$ is $T_2$, hence a branch, rather
   than $T_1=\beta$.
2. A beta leaf entered with counter $c$ has rank $c+1$, because
   $\rho^c\beta=T_{c+1}$.
3. $T_2=\langle\beta,\alpha\rangle$ replies $\alpha$ at $R$ and
   $\mathsf{absent}$ at $RL$.
4. If reply labels are erased, the total reached-address traces of
   $\alpha$ and $\beta$ coincide, so the four labelled languages are
   necessary for equality.
5. If the pair guard is removed, the equation $X=\rho X$ yields an
   infinite $J$-chain; the finite-administration and correspondence claims
   therefore do not extend to that unguarded syntax.

**Proof.** The first item is exactly the zero-update pair rule together with
native distribution. The second and third follow from (SPC.51). The fourth
holds because both finite leaves have no reached children. In the fifth item,
$J_{d,X}$ has no finite remainder to reach a stable root, so the epsilon
chain never terminates. These checks delimit the construction; they are not
claims about all unguarded semantics or about decidability outside
Definition 13.1. $\square$

## 14. Concrete record interface for signed prescribed-row consumers

**Definition 14.1 (concrete records).** For a chart supplied by the complete
native correspondence of [PDC, Theorem 5.2][PDC] and the joint signed support
of [NAC, Definition 5.1 and Theorem 6.1][NAC], a record $d$ contains exactly:

1. For each scalar coordinate, either an exact label $\overline n=q$ with
   $q\in\mathbb N$ or an infinity label $\overline n=\infty$. The labels
   denote $T_q$ and $\Omega$, respectively.
2. A partition of residual coordinates into $F$ and $I$, an exact finite
   native tree $f_t$ for every $t\in F$, and a finite nullary pair-guarded
   system plus one output expression $O_t$ for every $t\in I$. Every such
   expression satisfies Definition 13.1. An $I$ output contains $\Omega$ or
   reaches a directed cycle in its defining dependency graph; this is the
   supplied witness that its completed value is genuinely infinite.
3. Shared systems occur once and are combined with independent systems only
   after disjoint renaming. Repeated chart names keep one value. No record
   asserts a point merely by naming an arbitrary completed tree.

The record denotes
$\operatorname{pt}(d)=(\mathbf t,\mathbf Z)$, with $t_a=T_{q_a}$ or $\Omega$
according to its scalar label, $Z_t=f_t$ for $t\in F$, and
$Z_t=\llbracket O_t\rrbracket$ for $t\in I$. Its effective prefix interface
$\operatorname{Pref}_d(t,h)$ returns every reply through inclusive depth $h$,
including root and absent replies: finite $f_t$ is evaluated directly, while
an $I$ output uses the supplied guarded iteration, with $h+1$ pair-guarded
iterations sufficient through depth $h$. This is an interface for supplied
records, not a representation of arbitrary completion points.

After all finite residuals are frozen, the chart's complete whole-negative
list is retained in one predicate $\Gamma$ on the full Cartesian residual
carrier. Positive, image and navigation conditions have already been
eliminated by the cited chart suppliers. With $K$ the exact remaining
Presburger condition, write

$$
\begin{aligned}
S_f(\mathbf n)&\Longleftrightarrow
 K(\mathbf n)\land\exists\mathbf w_I\in\mathcal T^I\;
 \Gamma(\mathbf n,(f_t)_{t\in F},\mathbf w_I),\\
\operatorname{Cof}(d)&\Longleftrightarrow
 \forall b\in\mathbb N\;\exists\mathbf n\in\mathbb N^k\quad
 S_f(\mathbf n)\land
 \bigwedge_{a\notin J}n_a=q_a\land
 \bigwedge_{a\in J}n_a\ge b,
\end{aligned}
\tag{SPC.56}
$$

where $J$ is the set of infinity-labelled scalars. One tuple of residuals
satisfies all whole negatives at the same scalar vector. Empty products and
conjunctions have their literal meanings; when $J$ is empty, cofinality is
fixed-rank feasibility.

**Theorem 14.2 (decidable supplied-record certificate and productive
finite witnesses).** For records $d_i,d_j$ in two distinct complete row
charts, define

$$
\operatorname{Accept}(d_i,d_j)\Longleftrightarrow
\operatorname{Cof}_i(d_i)\land\operatorname{Cof}_j(d_j)\land
Y_i(d_i)=Y_j(d_j),
\tag{SPC.57}
$$

where each $Y$ is the chart output obtained from the record, with fixed
source-template exponents and all shared references preserved. The predicate
(SPC.57) is decidable. If it holds, then for every inclusive depth $h$ there
are finite $u_h,v_h$ in the entire acquired domain with their prescribed,
distinct complete rows and $u_h\equiv_hv_h$. The witnesses and their finite
coordinate tuples may vary independently with $h.

**Proof.** Substitute each finite $f_t$ in every occurrence of $\Gamma$.
The remaining full Cartesian residual condition is exactly the fixed-power
Presburger support supplied by [URR, Corollary 3.2][URR], so both quantified
sentences in (SPC.56) are decidable with the displayed quantifier order.
The combined systems and outputs satisfy Definition 13.1; Theorem 13.5
decides the equality conjunct by four original-address language comparisons.
The chart correspondences of [PDC, Theorem 5.2][PDC] and [NAC, Definition 5.1 and Theorem 6.1][NAC]
then identify each cofinal record with its own complete row closure and
supply finite realizations at every requested depth. Their whole-negative
list, endpoint reach guards, old row, exterior, partitions, repeated names,
classes and cross-class inequalities remain checked on each finite source.
The supplied prefix interface makes the construction productive; raw
unfoldings alone do not replace the joint finite completion.

If cofinality is false, the same support theorem supplies a finite
coordinate neighborhood disjoint from that chart. If equality is false,
Theorem 13.5 supplies a finite original address with different replies.
Either failure rejects this supplied candidate pair only; it does not reject
another record or another distinct-label pair. The construction proves
neither description completeness nor a search procedure over all records.
$\square$

**Corollary 14.3 (equality-premise substitution).** Whenever a cited signed
consumer has an ordinary premise asserting equality of two completed outputs,
Theorem 13.5 may replace that premise for records satisfying Definition 14.1.
The remaining cofinality, finite freezing, joint support and whole-source
hypotheses are unchanged. The substitution does not produce an ordinary
finite equational derivation, a complete description language, or an
unrestricted contact solver.

## 15. Current scope and retained boundary

**Convention 15.1 (supplier ownership).** The one-counter construction and
its reply correspondence in Theorems 13.3--13.5 are repo-derived ordinary
mathematics. The exact classical supplier boundary is BGJ Theorem 3 together
with its Appendix pp.23--24. The concrete-record consumer reuses PDC's
complete signed charts, NAC's joint support/common-contact synthesis, URR's
full-Cartesian Presburger support and the existing closed-presentation
interface of Section 7. No external novelty or priority claim is made.

NAC's complete NIC exact-cover result supplies automatic common-contact
synthesis and total stopping within its stated finite chart class. NPL's
Theorem 5.3 decides the complete finite whole-row image; its infinite-image
branch excludes a finite $H$ through PDC Corollary 8.3. Those results do not
make the supplied-record checker complete for arbitrary semantic points.

The retained open boundary is arbitrary-description equality, including
parameter-recursive or unrestricted equality beyond fixed nonnegative
powers and finite nullary pair-guarded systems; exhaustive synthesis of all
records or all contacts; and the unrestricted signed stopping problem of
Open problem 10.1. Physical observer acquisition, complete-state factoring,
paid receipts, compact-input complexity, undecidability, novelty and
Lean/kernel certification are not claimed. A finite equality decision also
does not identify private completion holes of different residuals or turn
separate row witnesses into one source.

[BGJ]: https://arxiv.org/pdf/1301.2181v1
[PDC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_POSITIVE_DOMAIN_CORRESPONDENCE.md
[NAC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_AMBIENT_CONTACT_DECISION.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md

## 追加锚（本行以下为增补区）
