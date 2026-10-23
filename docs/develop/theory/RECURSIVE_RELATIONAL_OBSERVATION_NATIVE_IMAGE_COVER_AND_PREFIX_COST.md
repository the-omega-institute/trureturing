# Finite native image covers and the raw prefix-cost boundary

## 1. Native syntax and the required source domain

**Definition 1.1 (finite native algebra).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle,\\
T_j&=\rho^j\alpha\qquad(j\in\mathbb N).
\end{aligned}
\tag{NIC.1}
$$

Every tree is nonempty, finite and ordered. Pairing is the actual free
binary constructor of these trees. The symbol $\rho$ has the interpreted
laws in (NIC.1); it is not a free unary constructor. A native expression
uses a declared finite tuple $\mathbf x=(x_1,\ldots,x_d)$, finite ground
trees, pairing and supplied fixed natural powers of $\rho$. The declared
tuple includes variables unused in the expressions. Every occurrence of
one name denotes the same tree.

A positive presentation $\mathscr E(\mathbf x)$ is a finite conjunction
of native expression equalities. A signed presentation adds a finite list
$\Delta(\mathbf x)$ of whole-tree disequalities. Repetitions in either
list are retained. The empty conjunction is true, and $\mathcal T^0$
contains exactly the empty tuple. No source-size or source-depth bound is
part of these domains.

**Definition 1.2 (mixed native images).** For $k,m\ge0$, a mixed template
has grammar

$$
A::=g\mid T_{n_j+c}\mid\rho^a(z_i)\mid\langle A,A\rangle,
\qquad 1\le j\le k,\quad 1\le i\le m,
\tag{NIC.2}
$$

where $g$ is a fixed finite native tree and $a,c\in\mathbb N$ are fixed.
Its arguments range over $\mathbb N^k\times\mathcal T^m$, with repeated
names shared. A positive image piece consists of a tuple $F$ of such
templates and a conjunction $P$ of affine integer equalities in
$\mathbf n\in\mathbb N^k$. Its domain before signed tests is precisely

$$
\{\mathbf n:P(\mathbf n)\}\times\mathcal T^m.
\tag{NIC.3}
$$

The product includes accidental equalities among different $z_i$. There
are no residual shape restrictions, positive residual equations or
normality predicates in (NIC.3). A finite image cover means equality
with a finite union of these images. Different pieces and different
arguments of one piece may give the same original tuple. It provides no
unique coordinates or observable choice of piece or arguments.

## 2. Positive branch data and connected residual sorts

**Assumption 2.1 (the supplied normal algebra).** Use the bijection of
[ABC, Theorems 2.2–2.3][ABC]. Its ambient algebra, normal part and expansion
are

$$
\begin{aligned}
\mathcal K&::=[r]\ (r\in\mathbb N)\mid F(\mathcal K,\mathcal K),\\
E([r])&=T_r,&E(F(X,Y))&=\langle E(X),E(Y)\rangle,\\
F(X,Y)\in\mathcal N
&\Longleftrightarrow X,Y\in\mathcal N\ \land\
 \neg\exists r\ge0\ (X=[r+1]\land Y=[r]).
\end{aligned}
\tag{NIC.4}
$$

All primitives are normal. The canonical map $B:\mathcal T\to\mathcal N$
and $E|_{\mathcal N}$ are effective inverses. Translation $\tau_a$ adds
$a$ to every primitive rank and preserves $F$; it preserves normality.
Native pairing in $\mathcal N$ is

$$
J(X,Y)=
\begin{cases}
[r+2],&X=[r+1],\ Y=[r],\quad r\ge0,\\
F(X,Y),&\text{otherwise}.
\end{cases}
\tag{NIC.5}
$$

The supplied identities are $B(T_r)=[r]$,
$B(\rho^a u)=\tau_a B(u)$ and
$E(J(X,Y))=\langle E(X),E(Y)\rangle$ for normal $X,Y$.
The finite atomic recurrence is

$$
T_{r+2}=\langle T_{r+1},T_r\rangle\qquad(r\ge0).
\tag{NIC.6}
$$

Only on $\mathcal N$ is $E$ asserted injective. On the full ambient
algebra it is deliberately allowed to identify different codes.

**Definition 2.2 (positive flattening).** Name every declared input
variable and every subexpression of $\mathscr E$. Repeated uses of a
name reuse its value. Expand a fixed ground parameter into its finite
native syntax. The positive definitions become

$$
Z=[0],\quad Z=[1],\quad Z=\tau_a X,\quad Z=J(X,Y),
\tag{NIC.7}
$$

together with the original positive equalities between names. For each
$J$ definition choose a collapse case

$$
X=[r+1],\quad Y=[r],\quad Z=[r+2],\qquad r\in\mathbb N,
\tag{NIC.8}
$$

or an ordinary case $Z=F(X,Y)$. At this stage canonical solutions
require every name normal, including an ordinary case's output.

Erase ranks to a primitive shape $c$ and an ordered binary shape
constructor $f$. A shift gives equal shapes. A collapse forces the
three primitive shapes, an ordinary case gives $s_Z=f(s_X,s_Y)$,
and every other positive equality gives the corresponding shape
equality. Solve this finite free-shape problem by an idempotent most
general unifier $\sigma$, with its factorization property on the
entire declared family of shape names. In particular unconstrained names
are left independent; they are not identified merely because they do
not occur in an equation. Failure discards this case only. Write
$S_Z=\sigma(s_Z)$, retaining all names, including unconstrained names.
The residual variables occurring in this finite tuple of terms are
$w_1,\ldots,w_m$.

Finite free-tree unification and its factorization property are used
exactly as in [NSF, Definition 3.1][NSF]. Its occurs check applies to
these erased *branch* equations over $c,f$, never directly to an
interpreted native expression.

Decorate every explicit $c$ occurrence of each $S_Z$ with a natural
scalar $r_{Z,p}$ and every occurrence of $w_j$ with a block name
$U_{Z,p}$ of sort $j$. Different positions have different decorations;
reusing $Z$ reuses its entire decorated term. A block is a rank function
on the leaves of the nonempty finite shape eventually filling $w_j$.

**Definition 2.3 (positive comparison graphs).** Traverse the identical
shape terms in every required positive comparison. As supplied by
[NSF, Lemma 3.2][NSF], the resulting equations have only the forms

$$
r=r'+d,\qquad r=d,\qquad U=V+d,\qquad d\in\mathbb Z.
\tag{NIC.9}
$$

The last equation compares entire blocks of the same residual sort,
with pointwise rank offset. No comparison joins a block to a scalar or
blocks of different residual sorts. Constant and collapse equations
retain their actual natural scalars. In particular the $r$ introduced
in (NIC.8) is retained as a natural scalar.

For each residual sort form the undirected graph on all its block
occurrences, including isolated vertices, with one oriented offset edge
for every equation $U=V+d$. Traversing an edge backwards reverses its
offset. All occurrences in all named terms are included, not only
those visible in an eventual output.

**Lemma 2.4 (most-generality connects each residual sort).** In the data
of Definitions 2.2–2.3, the graph of each occurring $w_j$ is connected.

Proof. Suppose the graph of $w_j$ has at least two components. For each
component introduce a different fresh free shape variable. In every
$S_Z$, replace an occurrence of $w_j$ by the fresh variable of its block
component. Do this simultaneously for every disconnected sort, if any,
and leave $c,f$ unchanged. Use the same modified term every time the
same name $Z$ appears. Assigning these modified terms to the original
shape variables $s_Z$ defines a substitution $\sigma'$ into fresh
variables.

This is still a unifier of all original shape equations. Indeed, on the
two sides of a positive comparison the old terms were syntactically
identical. Corresponding residual occurrences are joined by the block
edge generated by that comparison, and therefore receive the same fresh
variable. Corresponding explicit leaves remain $c$ and corresponding
constructors remain $f$. For an ordinary definition the comparison is
between $S_Z$ and $f(S_X,S_Y)$; its corresponding occurrences are joined
in exactly the same way. For a shift it is between $S_Z,S_X$; constants
and collapse cases have only explicit $c$. Thus every defining and
original shape equality survives. There is no additional shape equation
left unexamined.

Most-generality of $\sigma$ gives a substitution $\theta$ with
$\sigma'(s_Z)=\theta(\sigma(s_Z))=\theta(S_Z)$ for every original name.
At any fixed occurrence of $w_j$ in $S_Z$, the right side consequently
has subtree $\theta(w_j)$. The left side has the fresh variable of that
occurrence's component. Two components both have vertices, each a
specified occurrence in some $S_Z$. Equality of the respective free
terms would force $\theta(w_j)$ to equal two different fresh variables.
That is impossible. Hence each sort is connected. This argument also
covers an unconstrained original name: its one residual occurrence is
included, even if the original variable is unused. $\square$

**Lemma 2.5 (one nonnegatively shifted base per sort).** A sort's block
equations are either inconsistent on every nonempty finite leaf set,
or have computable integer potentials $\delta_U$ such that all its
solutions satisfy

$$
U=U_0+a_U,\qquad a_U=\delta_U-\delta_{U_0}\ge0,
\tag{NIC.10}
$$

where $U_0$ is a vertex of minimum potential. In the consistent case,
every natural-valued base function $U_0$ on any nonempty finite shape
gives a solution by (NIC.10). If an actual canonical solution is given,
its block $U_0$ is a normal subcode and all its blocks are the
translations $\tau_{a_U}U_0$.

Proof. By Lemma 2.4 there is one connected component. Give one vertex
potential zero and propagate integer differences along edges. If a
cycle has nonzero signed sum, any function solution would at each leaf
satisfy $t=t+d$ with $d\ne0$, a contradiction. There is at least one
leaf, since every ground finite shape over $c,f$ is nonempty. Conversely,
if every cycle has zero sum, path sums are independent of the chosen
path and give potentials satisfying all edges. Every solution differs
from these potentials by one common function, by following paths.
Choosing a minimum-potential vertex gives (NIC.10), including $a_{U_0}=0$.
All $a_U$ are nonnegative, so any natural base remains natural and all
edges hold. These are finite graph operations.

In a canonical solution each occurrence is an actual subtree of a
normal code, hence normal. All blocks of the sort have the same ground
shape. Their pointwise differences in (NIC.10) therefore say exactly
that the codes are $\tau_{a_U}U_0$. Nonnegative translation of a normal
code is normal by Assumption 2.1. $\square$

## 3. The entire positive and signed images

**Lemma 3.1 (sound expansion without ambient normality).** For arbitrary
ambient codes $X,Y\in\mathcal K$ and $a\ge0$,

$$
E(F(X,Y))=\langle E(X),E(Y)\rangle,\qquad
E(\tau_a X)=\rho^a E(X).
\tag{NIC.11}
$$

Every positive flattened definition and positive equality is sound
under $E$, even when a filled ordinary code is nonnormal.

Proof. The first identity is the definition of $E$. On a primitive,
the second is $T_{r+a}=\rho^a T_r$. On $F(X,Y)$, use the two inductive
identities and preservation of native pairing by $\rho^a$ to obtain it.
This proves it by finite structural induction on $X$.

An ordinary definition expands by the first identity, a shift by the
second, and the constant definitions by $T_0=\alpha,T_1=\beta$.
A collapse definition expands to its native pairing equation by
(NIC.6). Thus either chosen case of a $J$ definition implies the
required native pairing identity after expansion. Equal ambient codes
have equal expansions, so positive comparisons are preserved too.
No inference in this proof uses injectivity of ambient expansion or
falsity of a native equality from ambient syntactic inequality.
$\square$

**Theorem 3.2 (universal finite positive-native image cover).** For every
finite positive presentation $\mathscr E$ in the entire declared tuple
$\mathbf x\in\mathcal T^d$, one can effectively construct a finite list
$(P_b,F_b)_{b\in\mathcal B}$ as in Definition 1.2, with possibly different
$k_b,m_b$, such that

$$
\operatorname{Sol}(\mathscr E)
=
\bigcup_{b\in\mathcal B}
\{F_b(\mathbf n,\mathbf z):
   \mathbf n\in\mathbb N^{k_b},\ P_b(\mathbf n),\
   \mathbf z\in\mathcal T^{m_b}\}.
\tag{NIC.12}
$$

Each $F_b$ has exactly $d$ output components, retaining every declared
variable. Both inclusions are over actual finite native assignments.
The cover may overlap and need not have unique arguments. Effectivity
here is a terminating finite mathematical construction from the supplied
finite syntax, with no uniform bound on its image's sources.

Proof. Perform Definition 2.2 on the whole declared tuple. There are
finitely many collapse choices and finitely many finite shape problems.
Discard a failed shape case. In a successful case form all decorations
and comparisons of Definition 2.3, without making negative choices or
replacing residual shapes by markers. Discard a case with an inconsistent
block cycle, as justified by Lemma 2.5.

For each remaining residual sort $j$, choose the minimum-potential
vertex $U_{j,0}$. Introduce an independent native parameter $z_j$.
Replace every occurrence block $U$ of this sort by
$\tau_{a_U}B(z_j)$, with the same replacement at repeated uses of that
block. This is allowed for every $z_j\in\mathcal T$, with no relation to
another sort. The parameters may have equal shapes or equal native
values across different sorts.

Enumerate all explicit scalar decorations and all natural collapse
scalars as parameters $n_1,\ldots,n_k$. Keep their scalar offset and
constant equations, including all of (NIC.8), as $P(\mathbf n)$.
The requirements that they be natural are in $\mathbb N^k$ itself.
These are affine integer equalities. An inconsistent scalar case may
be retained with an empty arithmetic domain or discarded by solving its
finite offset system. Neither choice changes its image.

After these replacements each name has an ambient code template built
from $[n_j]$, $F$ and $\tau_a B(z_i)$. Its positive comparisons hold
for all $P(\mathbf n)$ and all native $\mathbf z$: traverse the compared
terms. Explicit leaves agree by $P$; residual blocks satisfy every edge
by (NIC.10); matching $F$ nodes reconstruct the equal codes. The same
traversal handles a shift by adding its fixed offset at every leaf.
It handles an ordinary definition by matching $F$ at the root and
handles primitive definitions by their scalar equations.

Now *omit* all canonical normality restrictions on these assembled
ambient codes. Their expansion remains sound by Lemma 3.1. In
particular, a former ordinary case may now fill as
$F([r+1],[r])$; it expands to $T_{r+2}$ and still satisfies the native
pairing equation. The case is no longer asserted to record the canonical
collapse choices of this filling. That loss of canonical branch identity
creates overlap, not an extra native solution.

Expand the ambient template of each original $x_i$. An explicit
primitive gives $T_{n_j}$, a residual block gives $\rho^{a_U}z_j$, and
$F$ gives actual pairing. Constants can be retained as fixed ground
trees. These are precisely mixed templates (NIC.2). Induction through
the named subexpression definitions shows that their expanded values
are the evaluations of the original expressions at these expanded
$x_i$. Every original positive equality is one of the preserved
comparisons. Thus every output $F_b(\mathbf n,\mathbf z)$ in (NIC.12)
satisfies $\mathscr E$. This proves soundness for arbitrary finite
parameter values, including nonnormal assembled codes.

For completeness take any original $\mathbf x\in\operatorname{Sol}(\mathscr E)$. Evaluate all named subexpressions and apply $B$ to their
actual values. Their genuine smart-constructor cases choose one of the
finite branches. Their finite ground shapes solve that branch's shape
equations and hence factor through its most general unifier. Read the
actual natural ranks at every explicit leaf and the actual collapse
scalars. They satisfy $P$ with their original values.

For a residual sort the actual blocks have a common finite ground shape
and satisfy all its offset equations. There is no nonzero cycle. At
the chosen minimum vertex the actual block is normal. Set
$z_j=E(U_{j,0})$, so $B(z_j)=U_{j,0}$. Lemma 2.5 reconstructs every
actual block as $\tau_{a_U}B(z_j)$. With the actual explicit ranks this
recovers the entire canonical code of *every* name, not merely its
shape. Expanding the original names therefore gives the original tuple
$\mathbf x$ itself. No bound, shape marker or canonical filling is
substituted for that source. This proves the other inclusion.

All branch operations are finite syntactic, graph or integer operations,
and finite free-shape unification terminates. The native templates are
finite descriptions even though their arguments and expanded values
have no common size bound. An unused original variable has its name and
unconstrained residual sort and is recovered in exactly the same way.
For $d=0$ the output tuple is empty; a ground successful presentation
has that tuple as its image and an inconsistent one has no image. For
an empty presentation the construction is also valid; in particular
one may take $k=0,m=d$, $P$ true and $F(\mathbf z)=\mathbf z$.
All zero-dimensional products have their singleton meaning. $\square$

**Theorem 3.3 (original-native signed pullback).** For any additional
finite disequality list $\Delta$, with the same positive cover as in
Theorem 3.2, put

$$
C_b(\mathbf n,\mathbf z)
\Longleftrightarrow
P_b(\mathbf n)\ \land\ \Delta(F_b(\mathbf n,\mathbf z)).
\tag{NIC.13}
$$

Each negative in (NIC.13) is evaluated in the native algebra after
expansion. Then

$$
\operatorname{Sol}(\mathscr E\land\Delta)
=
\bigcup_b\{F_b(\mathbf n,\mathbf z):C_b(\mathbf n,\mathbf z)\}.
\tag{NIC.14}
$$

Every finite Boolean combination of native equalities has such a finite
signed mixed-image cover, retaining all declared variables.

Proof. An image point with $C_b$ satisfies the positive presentation by
Theorem 3.2 and satisfies each original negative by its literal native
test in (NIC.13). Conversely take an original signed solution. The
completeness construction in Theorem 3.2 returns its *same* original
tuple. Consequently every one of its original negative tests still
holds on that tuple. These are both inclusions in (NIC.14). For a
Boolean formula take finite disjunctive normal form, retaining the
whole original declared tuple and repeated atom occurrences in every
conjunction, and apply the
argument to each conjunction. A false disjunct contributes nothing;
an empty signed conjunction has its usual truth value. $\square$

**Proposition 3.4 (noncanonical codes and interpreted feedback).** The
soundness in Theorem 3.2 does not justify using ambient shape or code
inequality as a negative test. Its branch occurs checks do not reject
all interpreted native feedback equations.

Proof. The different ambient codes $F([1],[0])$ and $[2]$ expand to the
same actual tree $\langle\beta,\alpha\rangle=T_2$. Thus their ambient
inequality is not a native disequality, exactly why (NIC.13) is imposed
after expansion.

The native equation $\rho x=\langle x,\alpha\rangle$ has the finite
witness $x=\beta$. Its actual code definitions choose the collapse with
$X=[1]$, the other argument $[0]$ and output $[2]$; their erased shapes
are all $c$, so this positive branch is not rejected by a free occurs
check. More generally (NIC.6) makes
$\rho^2(T_j)=\langle\rho(T_j),T_j\rangle$ true for every $j\ge0$.
These are actual finite interpreted solutions. The proof of Theorem
3.2 preserves them through their genuine branches. $\square$

**Proposition 3.5 (credited Cartesian negative completion).** For each
signed piece (NIC.13), [URR, Theorem 3.1 and Corollary 3.2][URR] supplies a
finite tuple $\mathbf z_b^\star$, independent of $\mathbf n$, and a
Presburger formula $\Psi_b$ such that

$$
\begin{aligned}
\exists\mathbf z\ C_b(\mathbf n,\mathbf z)
&\Longleftrightarrow C_b(\mathbf n,\mathbf z_b^\star)\\
&\Longleftrightarrow P_b(\mathbf n)\land\Psi_b(\mathbf n).
\end{aligned}
\tag{NIC.15}
$$

This is a rank-support section, not an image identity after fixing
$\mathbf z=\mathbf z_b^\star$, and it preserves no arbitrary prescribed
original prefix of a represented source.

Proof. Substitution of $F_b$ into any original expression gives a mixed
template: distribute each fixed power through pairs and finite ground
trees, add it to the offsets in $T_{n_j+c}$, and combine it with a
residual decoration $\rho^a z_i$. All decorations remain nonnegative.
Thus the pulled-back list $\Delta(F_b)$ has exactly URR's grammar with
shared names. By Theorem 3.2 the domain before negatives is the full
Cartesian product in (NIC.3); there is no hidden positive residual
restriction to violate URR's hypothesis. URR's equality reflection
therefore realizes all these negatives jointly at its one finite tuple
for every feasible rank, and its arithmetic equality analysis gives
$\Psi_b$. Conjoining the rank-only $P_b$ proves (NIC.15).

For the distinction, take the identity cover of the empty presentation
in one variable, with $k=0,m=1$ and no negatives. Its source image is
all of $\mathcal T$. Fixing any one $z^\star$ gives only that single
source. A different finite source disagrees with it at some finite
original address. Hence the completion statement cannot also assert
preservation of every prescribed source prefix or of its entire image.
The exact signed image remains (NIC.14). $\square$

## 4. Complete acquired sources and exact finite-row strata

**Definition 4.1 (rows and signed guards).** An address is a finite word
in $\{L,R\}^*$, with root $\varepsilon$. The reply $r_u(p)$ is
$\alpha,\beta,\mathsf{branch}$ or $\mathsf{absent}$. A subtree $u|_p$
exists exactly at reached addresses. For a finite prefix-free original
cut $A$, the complete row $R_A(u)$ has three fields: the ordered reached
set $I_A(u)=A\cap\operatorname{Pos}(u)$, the concrete ordered exterior
$C_A(u)$ with numbered holes at those addresses, and the full equality
partition of their entire native subtrees. Empty cuts, the root cut and
absent cut addresses are included.

Its native mask is $M_A(u)=C_A(u)[\alpha,\ldots,\alpha]$. The reached set
and mask recover the exact exterior by replacing the subtrees at those
known reached addresses by the corresponding numbered holes. This is
[ABC, Theorem 4.2][ABC]; no equality partition is inferred from a mask.

For a signed record $e=(a,p,b,q,\bowtie)$, $\bowtie\in\{=,\ne\}$, define

$$
\operatorname{Rel}_e(u)
\Longleftrightarrow
p\in\operatorname{Pos}(\rho^a u)\ \land\
q\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q.
\tag{NIC.16}
$$

Either sign requires both guards. In particular an absent endpoint does
not satisfy a negative record. A literal $(a,p,c)$ imposes
$r_{\rho^a u}(p)=c$. The entire source fiber for a fixed old row $R$,
finite literal list $H_0$ and finite signed list $H_{\rm rel}$ is

$$
D=\{u\in\mathcal T:
R_P(u)=R,\ H_0(u),\ \bigwedge_{e\in H_{\rm rel}}\operatorname{Rel}_e(u)\}.
\tag{NIC.17}
$$

All lists retain repetitions, all constraints refer to the same original
$u$, and no old class or inequality is restricted to the new task $Q$.
If old holes $i,j$ have one class, their entire subtrees must agree;
if they have different classes, their entire subtrees must differ,
including classes outside the new cut. The old concrete exterior and
old absent addresses are also part of (NIC.17).

**Assumption 4.2 (paid complete handoff and actual actions).** In service
applications impose [ARH, Assumption 1.3][ARH]. All retained records and
the old row were acquired by paid legal operations and comparisons.
The same original-root physical register has authentically reached
$\rho^N u$, where $N$ is common and at least all recorded epochs. The
complete accessible state is a common recoverable encoding of the
retained input and common parameters, with exact original-source fiber
$D$. Every accessible source-bearing cache, address, count, length,
program position, timing field, output, archive, permission and handle
belongs to that retained state. Pre-cut acquisition need only terminate
on each actual source; no common pre-cut cost bound is imposed.

A legal service is deterministic and effective, correct and terminating
on every $u\in D$. Its source actions are paid original-root
$\mathsf{Read}(p)$ for any finite physical word $p$, forward
same-register $\mathsf{ApplyRho}$, and variable absorbing
$\mathsf{Halt}$. Halt may depend on acquired replies and local state.
No reset, clone, reroot, source cutoff, rank, equality, chart-membership,
source identity or unknown-parameter port is present. Local computation
and updates add no source-dependent information. The mathematical
arguments of an image cover are not service observations.

For a service $A$ define, on each actual run,

$$
\begin{aligned}
v_A(u)&=(q_A(u),a_A(u),\ell_A(u)),&
\ell_A(u)&=\sum_{\text{actual reads at }p}|p|,\\
b(A)&=(\sup_D q_A,\sup_D a_A,\sup_D\ell_A),&
W_\lambda(A)&=\sup_{u\in D}\lambda\cdot v_A(u),\quad
\lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{NIC.18}
$$

Every raw read counts, including absent and repeated reads. A root read
has one call and zero address length. The coordinate-worst vector and
the same-run weighted value remain separate; zero weights are allowed.
Other acquisition, computation, retention and installation charges remain
separate from these coordinates.

**Theorem 4.3 (complete original-source signed image strata).** Fix the
input of Definition 4.1 and any complete finite row label $r$ at $Q$.
One can construct finitely many source templates $U_{r,b}$ and predicates

$$
C_{r,b}(\mathbf n,\mathbf z)
=P_{r,b}(\mathbf n)\land\Delta_{r,b}(\mathbf n,\mathbf z)
\tag{NIC.19}
$$

of the form in Theorem 3.3 such that

$$
D_r:=\{u\in D:R_Q(u)=r\}
=\bigcup_b\{U_{r,b}(\mathbf n,\mathbf z):C_{r,b}(\mathbf n,\mathbf z)\}.
\tag{NIC.20}
$$

Every produced source satisfies all retained records with both guards,
the entire old row and exactly the finite row label $r$. Conversely
every original $u\in D_r$ is reconstructed as that same source.

Proof. Apply the finite fixed-navigation decomposition of [NSF, Lemma
5.1][NSF] to the entire predicate in (NIC.17) and $R_Q(u)=r$. Here are
the concrete data preserved by that application. Choose a finite
original prefix depth strictly beyond all finitely listed cut positions
and record endpoint lengths. Enumerate its finite native prefix
patterns, with independent frontier variables at its reached boundary.
A source has its actual pattern and actual frontier subtrees; filling
these returns that very source. Repeated references to the source use
the same pattern and variables, not independent copies.

At each fixed epoch and endpoint, navigation through the transformed
pattern either yields a native expression in those frontiers, yields a
subtree of the explicitly transformed early ground leaf, or is absent.
No requested endpoint enters an unspecified frontier, because its
address is shorter than the chosen original depth. Fixed powers preserve
original branch nodes and expand early leaves by explicitly finite trees.
Thus guards and literal replies are decided exactly in each case. An
absent endpoint rejects either signed record, and a reached pair retains
its entire native equality or disequality. Repetition retains the same
expression wherever that endpoint is used.

For either old or new row fix the actual reached set of the case and
construct its mask expression by replacing exactly those subtrees by
$\alpha$. Every uncut frontier remains in that expression. Equality to
the label's concrete filled mask, together with equality of reached
sets, gives precisely its complete exterior. For every two reached
holes retain the equality required by the label's partition or the
disequality required by different classes. This includes all old
cross-class pairs, all repeated class occurrences and all off-task
inequalities. Empty reached sets and one-hole partitions have their
literal empty pair lists. Consequently the finite case formula retains
both complete partitions and masks, rather than projecting to selected
partition bits.

Each surviving case therefore has a finite native source term
$W(\mathbf x)$ and a Boolean native formula $\Phi(\mathbf x)$, with
both directions just described. Keep every frontier and definitional
auxiliary in its declared tuple. Convert $\Phi$ to finite signed
conjunctions and apply Theorems 3.2–3.3. Substitute their whole-tuple
image into $W$. The result is a mixed source template: fixed native
powers distribute through pairs, add to atomic ranks and combine with
residual decorations. All negatives in the complete case formula are
still native tests after this substitution.

For a satisfying parameter tuple, Theorem 3.3 supplies a satisfying
whole case assignment; filling $W$ gives a finite original source with
the decided guards, reached sets, masks, all partition bits and records.
For an original $u\in D_r$, choose its actual prefix and frontiers.
Theorem 3.3 reconstructs that same assignment, including auxiliaries,
and hence $W$ reconstructs $u$ itself with its original finite row.
These prove both inclusions in (NIC.20). All cases and templates are
finite. $\square$

**Assumption 4.4 (finite complete target image).** For the finite-pair
consumer assume $R_Q(D)$ is finite. Use its exact distinct list
$r_1,\ldots,r_s$, allowing $s=0$ when $D$ is empty. This list and actual
original realizers are supplied by [NPL, Theorem 5.3][NPL], which also
decides the finite-image premise from the input (NIC.17). The premise
does not require that $D$ itself be finite. Each $r_i$ contains its
concrete exterior, reached set and full finite-source partition.

The finite-image premise is necessary for prefix determination and
therefore gives an exact reduction of the general input. For any fixed
$h$ there are only finitely many words $|p|\le h$, hence only finitely
many four-valued prefix reply tuples. If that depth determines a row,
there is at most one row per such tuple, so the complete row image is
finite. Thus NPL's infinite-image outcome excludes every determining
depth; its finite-image outcome retains the entire original $D$ for
Theorem 5.2, rather than selecting a finite source sample.

## 5. Exact signed pair predicates and the missing stopping alternative

**Definition 5.1 (inclusive original prefixes).** Write

$$
u\equiv_h v
\Longleftrightarrow
\forall p\in\{L,R\}^*,\quad |p|\le h\ \Longrightarrow\ r_u(p)=r_v(p),
\tag{NIC.21}
$$

including the absent reply. Let $\operatorname{PrefDet}(D,Q,h)$ mean
that $u\equiv_h v$ for $u,v\in D$ implies $R_Q(u)=R_Q(v)$.
For the pieces of Theorem 4.3 and Assumption 4.4 define, whenever $i\ne j$,

$$
\begin{aligned}
J_{ib,jc}(h)\Longleftrightarrow
\exists\mathbf n,\mathbf z,\mathbf n',\mathbf z'\quad&
C_{r_i,b}(\mathbf n,\mathbf z)\land
C_{r_j,c}(\mathbf n',\mathbf z')\\
&\land\ U_{r_i,b}(\mathbf n,\mathbf z)
       \equiv_h U_{r_j,c}(\mathbf n',\mathbf z').
\end{aligned}
\tag{NIC.22}
$$

All natural and residual tuples have their own piece's dimensions and
range over actual finite values. They are independent across the two
sources except for the displayed joint prefix condition. Each piece
retains sharing within its own original source.

**Theorem 5.2 (finite-pair exactness at every depth and at all depths).**
Under Assumption 4.4, for every $h\ge0$,

$$
\neg\operatorname{PrefDet}(D,Q,h)
\Longleftrightarrow
\bigvee_{i\ne j,b,c}J_{ib,jc}(h).
\tag{NIC.23}
$$

Moreover,

$$
\begin{aligned}
\forall h\ \neg\operatorname{PrefDet}(D,Q,h)
&\Longleftrightarrow
\exists(i,b,j,c),\ i\ne j,\ \forall h\ J_{ib,jc}(h),\\
\exists h\ \operatorname{PrefDet}(D,Q,h)
&\Longleftrightarrow
\forall(i,b,j,c),\ i\ne j,\ \exists H\ \neg J_{ib,jc}(H).
\end{aligned}
\tag{NIC.24}
$$

The persistent-pair statement on the first line requires actual finite
original witnesses with their exact different complete row labels at
each $h$. It does not require one fixed witness pair for all $h$.

Proof. If prefix determination fails, take its original finite witnesses
$u,v\in D$ and their different exact labels $r_i,r_j$. The two
completeness directions of Theorem 4.3 reconstruct those sources in
some pieces $b,c$. Their original prefix agreement gives (NIC.22).
Conversely a satisfying parameter tuple in (NIC.22) expands by the two
soundness directions to finite $u,v\in D$ with exactly $r_i,r_j$.
These labels differ, and (NIC.21) is their actual original prefix
agreement. This proves (NIC.23) on the entire domain in both directions.

There are finitely many row-piece pairs. Each $J$ is downward closed
in $h$: witnesses at a larger depth also witness every smaller depth.
If no pair persists at every depth, choose a failed depth $H$ for each
pair and take their finite maximum. Downward closure means that each
pair still fails at this maximum and at every larger depth. Equation
(NIC.23) then gives a determining depth. Conversely a persistent pair
gives failure at every $h$ by the same equation. Negating this alternative
gives the second line of (NIC.24). With no row-piece pairs take maximum
zero; then prefix determination is vacuous at every depth. This includes
empty $D$ and one-label images. At no step is a finite equality partition
recomputed on a common infinite limit. $\square$

**Proposition 5.3 (exact finite feasibility and its scope).** Each supplied
finite $h$ has a terminating feasibility decision in the original
question (NIC.23). For any one piece-pair its predicate (NIC.22) also
has a terminating finite feasibility decision. Neither statement provides
a terminating choice in the all-depth alternative of (NIC.24).

Proof. For (NIC.23) apply [NSF, Lemma 5.1 and Theorem 5.2][NSF] to two
independent source variables, each subject to the *whole* predicate
(NIC.17), and impose agreement at the finitely many original words
$|p|\le h$ and inequality of their complete rows. All coordinates and
all epochs are supplied finite values.

For a fixed piece-pair, choose finite original prefix patterns for
its residual variables strictly beyond $h$. Fixed residual decorations
$\rho^a z_i$ are then handled by the same finite navigation cases.
Variable-rank atoms require a further finite arithmetic split. At an
atom $T_r$, the cases $r=0$, $r=1$ and $r\ge2$ give respectively
$\alpha$, $\beta$ and, by (NIC.6),
$\langle T_{r-1},T_{r-2}\rangle$. For a supplied address, recurse on its
remaining letters, decreasing that length at each step. Each reached
atomic remainder has a natural rank $q=n_j+c-d$ for a fixed integer
$d\ge0$ in that case, represented by the affine equality
$q+d=n_j+c$ with a natural auxiliary $q$. A lower bound $q\ge2$ can
likewise be represented by $q=t+2$ with natural $t$. A path extending a
terminal leaf has the absent reply; at a reached remainder its root
label is decided by the same three rank cases. Thus finitely many
Presburger cases evaluate every literal in the supplied inclusive
prefix, including absence, without bounding the unknown ranks. On each
case the remaining whole-tree conditions are native mixed expressions
with natural atomic rank parameters, together with affine scalar
conditions. Apply the scalar-preserving extension of NSF described in
[URR, Corollary 3.2, proof][URR]: a primitive definition $Z=[n_j+c]$ has primitive shape
$c$, and its scalar offsets enter the same finite arithmetic systems.
The actual designated scalars are retained in NSF's completeness proof
when it replaces residual blocks. Conjoin both $P$ predicates to those
systems and existentially quantify their scalar auxiliaries and designated
scalars. Presburger feasibility terminates; NSF's soundness expands a
finite native witness, and its completeness keeps every designated
scalar and all signed constraints. Thus the decision applies to the
fixed piece-pair, without using a rank-dependent cutoff. All recovered
parameter values are finite.

These procedures take $h$ as input. Repeating NO answers for increasing
$h$ cannot by itself certify that no determining depth exists; nor does
repeating YES answers for one pair certify its all-depth persistence.
The finite monotonicity proof in Theorem 5.2 supplies an equivalence,
not a bound for the first failed depth or a complete finite persistence
certificate. $\square$

**Proposition 5.4 (the existing service consequence, with unchanged
charges).** Under Assumptions 4.2 and 4.4, with $D\ne\varnothing$, a
uniform finite-new-read legal service exists exactly when every
row-piece pair has a finite exclusion depth in (NIC.24). A persistent
pair supplies finite original counterpairs to every purported such
service. No new minimum of (NIC.18) follows.

Proof. [ARH, §2, (ARH.2.3) and its proof][ARH] gives, on exactly the
complete common-state and authentic-epoch premises of Assumption 4.2,
equivalence between a uniform finite-new-read serial service, such a
static service and an original determining prefix depth. Its
serial-to-prefix direction considers every deterministic effective
source-total controller with arbitrary finite-word reads and variable
absorbing halt, and uses a finite reply tree under a common read bound.
Original-prefix locality applies also to born and absent addresses.
Thus a claimed bounded service entails some finite $h$. A persistent
pair at that $h$, reconstructed by Theorem 5.2, contradicts its claimed
complete output.

Conversely, finite exclusion depths give their maximum determining
$h$. ARH's positive direction uses actual reads at the authentic static
epoch $N$ to recover this inclusive original prefix, then a finite-source
enumeration which terminates on each actual conditioned source fiber
and outputs its common full row. Its correctness uses membership in
the entire (NIC.17), not an image parameter observed at runtime. This
reuses the supplied legal service construction and paid interface.
The existence equivalence does not identify optimal read, update or
length coordinates and does not replace a same-run weighted supremum
by a sum of coordinate suprema. $\square$

**Open problem 5.5 (terminating signed joint finite approximability).**
For every piece-pair (NIC.22) arising from the complete acquired
construction, find a terminating choice between a finite $H$ proving
$\neg J_{ib,jc}(H)$ and a finite proof-bearing description producing
actual finite parameter witnesses for $J_{ib,jc}(h)$ for every $h$.
The latter must retain both entire signed predicates and both exact
finite-source row labels jointly. Theorems 3.2–5.2 do not supply this
choice. A limit partition, a residual-support section from URR, or a
supplied-context minimum-depth certificate is not assumed to preserve
the required joint prefixes. This is the original unrestricted stopping
obligation of [NLC, Open problem 9.2][NLC] and [NFO, Open problem 8.4][NFO].
The actual arbitrary-word action and resource optimization questions
remain separate; no new optimum is asserted here.

## 6. A self-contained obstruction for raw regular threshold cuts

**Definition 6.1 (canonical finite padding).** Let the native ranked
alphabet be $\Sigma=\{\alpha^{(0)},\beta^{(0)},\mathsf b^{(2)}\}$,
where $\mathsf b$ denotes pairing. Put
$\Lambda=\{\alpha,\beta,\mathsf b,\bot\}$, with $\bot$ an absent
coordinate, not a native leaf. The convolution alphabet $\Gamma$ has
one symbol $(a,b)$ for every pair in $\Lambda^2\setminus\{(\bot,\bot)\}$.
Its arity is two if at least one coordinate is $\mathsf b$, and zero
otherwise.

For finite original $u,v$, $\operatorname{conv}(u,v)$ has domain
$\operatorname{Pos}(u)\cup\operatorname{Pos}(v)$ and at each address
has the pair of their native root labels, using $\bot$ when that
coordinate is absent. Its two children are present exactly when at
least one source branches there. Thus its labels have precisely their
$\Gamma$ arities. There is no trailing padding below an address absent
in both sources. Let

$$
W=\{\operatorname{conv}(u,v):u,v\in\mathcal T\}.
\tag{NIC.25}
$$

All members of $W$ are finite trees, and both original roots are present.
Regular means recognized by a finite bottom-up tree automaton over this
finite ranked alphabet. A subset of $W$ is regular relative to $W$ if
it is the intersection of $W$ with such a regular language.

**Definition 6.2 (coordinate projections).** With an additional output
constant $\bot$, define the homomorphism $\pi_i$ for $i=1,2$ by taking
$a_i$ to be coordinate $i$ of a symbol $\gamma$. On a rank-two symbol
set

$$
\pi_i(\gamma(x_1,x_2))=
\begin{cases}
\mathsf b(\pi_i x_1,\pi_i x_2),&a_i=\mathsf b,\\
a_i,&a_i\in\{\alpha,\beta,\bot\},
\end{cases}
\tag{NIC.26}
$$

and on a rank-zero symbol set $\pi_i(\gamma)=a_i$. Erasing two children
when a coordinate is a leaf or absent is intentional. Each input child
occurs at most once in the homomorphism pattern. On $W$, $\pi_1$ and
$\pi_2$ recover precisely the two original native trees and contain no
output $\bot$.

**Lemma 6.3 (regular universe, exact projections and their regular
images).** The language $W$ is regular. Both projections are exact on
$W$, and the projection of any regular $L\subseteq W$ is a regular
native-tree language. Relative regular subsets of $W$ are closed under
complement within $W$ and intersection.

Proof. An explicit finite grammar checks canonical padding. Use
nonterminals indexed by the expected presence bits $(e_1,e_2)$,
excluding $(0,0)$. At a node choose a symbol whose coordinate is $\bot$
exactly when the corresponding expected bit is zero, and otherwise is
one of $\alpha,\beta,\mathsf b$. If neither coordinate branches, this
is a rank-zero production. If one branches, make both child
nonterminals have presence bits
$(\mathbf1_{a=\mathsf b},\mathbf1_{b=\mathsf b})$, the same bits for
left and right. Start with $(1,1)$. These finitely many productions
recognize exactly $W$: induction gives one absent or complete finite
native tree in each coordinate, and every canonical convolution follows
them. Finite regular grammars and bottom-up automata describe the same
finite-tree languages, by reading a production as a transition.

For projection exactness, at a coordinate's branch the two children
are both present in that coordinate, so induction returns its true two
native subtrees. At its leaf all children contributed only by the other
coordinate are erased. An absent coordinate similarly returns only
$\bot$ at that root. Since the roots of a $W$ tree both have presence
one, induction gives the original native outputs, with no retained
$\bot$ below their branches.

Here is the regular-image construction, specialized to (NIC.26).
Remove unproductive states from a bottom-up automaton for $L$. For each
remaining state $q$ introduce a grammar nonterminal $q$. A rank-two
transition $\gamma(q_1,q_2)\to q$ with projected coordinate
$\mathsf b$ yields $q\to\mathsf b(q_1,q_2)$. If that coordinate is
$a\in\{\alpha,\beta,\bot\}$, it yields $q\to a$. A rank-zero
transition yields its projected constant. Use the accepting states as
start nonterminals. Each generated output has an input witness: in an
erasing production choose any original witnesses for the productive
child states, and in a branch production combine the inductively
recovered child witnesses using the indicated original transition.
Conversely every accepting input run projects by exactly these
productions. Thus the grammar recognizes $\pi_i(L)$ in both directions.
On $L\subseteq W$ it contains only native trees, by the preceding
exactness. This is the linear, possibly erasing homomorphism construction
of [TATA, Theorem 1.4.3][TATA], with no copying of a child.

For completeness of the set operations, determinize a finite bottom-up
automaton by assigning to a subtree the set of all old states reachable
there. A symbol computes its parent set from the finite child sets;
acceptance means that the root set meets the old accepting states.
This finite complete deterministic automaton has the same language.
Changing accepting to nonaccepting states recognizes its complement.
A product of two automata recognizes intersection. Applying these
constructions with the regular $W$ proves the relative statements.
These are the constructions of [TATA, §§1.1 and 1.3][TATA]. $\square$

**Definition 6.4 (the entire accepted three-label family).** Put

$$
F(y)=\langle\alpha,y\rangle,\qquad
U(x,y)=\langle x,\langle y,F(y)\rangle\rangle,\qquad
D^*=\{U(x,y):x,y\in\mathcal T\}.
\tag{NIC.27}
$$

Here $F$ is a unary native context operation, distinct from the binary
ambient constructor in (NIC.4) and the tuples $F_b$ in (NIC.12).
Use exactly the acquired family of [NLC, Definition 8.1 and Lemma
8.2][NLC]: old cut $P=\{\varepsilon\}$ with its one-hole row, literals

$$
(0,\varepsilon,\mathsf{branch}),\quad
(0,R,\mathsf{branch}),\quad
(0,RR,\mathsf{branch}),\quad
(0,RRL,\alpha),
\tag{NIC.28}
$$

and signed record $(0,RL,0,RRR,=)$. The original target is
$Q=\{L,RL,RR\}$. Its three labels $r_0,r_1,r_2$ share the reached set
$Q$ and the concrete exterior
$\langle\square_1,\langle\square_2,\square_3\rangle\rangle$.
Their partitions are, respectively,
$\{\{1,2\},\{3\}\}$, $\{\{1,3\},\{2\}\}$ and
$\{\{1\},\{2\},\{3\}\}$. They are the entire complete row image,
including $r_2$; no selected two-label promise is imposed.

Define the entire different-row language inside $W$ by

$$
E^*=\{\operatorname{conv}(u,v):u,v\in D^*,\ R_Q(u)\ne R_Q(v)\}.
\tag{NIC.29}
$$

For distinct finite originals define

$$
\delta(u,v)=\min\{|p|:r_u(p)\ne r_v(p)\},
\tag{NIC.30}
$$

using all four replies. Set $\delta(u,u)=\infty$. Distinct finite trees
have a finite first disagreement, by recursion through their constructors.
The raw discrepancy cost on *all* $W$ is

$$
c(\operatorname{conv}(u,v))=
\begin{cases}
\delta(u,v)+1,&\operatorname{conv}(u,v)\in E^*,\\
0,&\operatorname{conv}(u,v)\in W\setminus E^*.
\end{cases}
\tag{NIC.31}
$$

It is a mathematical original-prefix discrepancy statistic. It is not
an optimum over paid actions or services.

**Lemma 6.5 (exact family, labels and finite-$y$ regular images).** The
entire fiber of (NIC.28) and its guarded record is $D^*$. Its exact
$r_0$ and $r_1$ strata are

$$
D_0^*=\{U(y,y):y\in\mathcal T\},\qquad
D_1^*=\{U(F(y),y):y\in\mathcal T\},
\tag{NIC.32}
$$

and the $r_2$ stratum is given by $x\ne y$ and $x\ne F(y)$.
For every regular native language $H\subseteq D^*$, the set

$$
Y_H=\{y:\exists x\ U(x,y)\in H\}
\tag{NIC.33}
$$

is finite.

Proof. The literals force the original skeleton
$\langle x,\langle y,\langle\alpha,z\rangle\rangle\rangle$.
Both endpoints of the signed equality are reached, and their whole
subtrees are $y,z$. Thus the record forces $y=z$, and conversely every
$U(x,y)$ satisfies the old root row, literals and both guards. At $Q$
the hole values are exactly $x,y,F(y)$. Since $F(y)$ has one more leaf
than finite $y$, these last two values differ. The three stated
partitions are therefore exhaustive with exactly the displayed
conditions. The first two are attained for each $y$. The third is
attained, for example, by $y=\alpha,x=\beta$. This proves the source
and label statements directly, agreeing with [NLC, Lemma 8.2 and
Proposition 8.5][NLC].

Take a complete deterministic bottom-up automaton for $H$, using the
subset construction recalled in Lemma 6.3 if needed. Denote the state
of a native subtree $y$ by $q(y)$. For any $y,z\in Y_H$ with the same
state choose an accepted $U(x,y)$. Replace only the occurrence of $y$
at address $RL$ by $z$, leaving $x$ and the copy at $RRR$ unchanged.
Determinism propagates the unchanged state to the root, so the result
$\langle x,\langle z,\langle\alpha,y\rangle\rangle\rangle$ is still
accepted. Containment $H\subseteq D^*$ forces its subtrees at $RL,RRR$
to agree. Thus $z=y$. The state map is injective on $Y_H$, so $Y_H$ has
at most as many elements as this finite automaton has states. In
particular every regular projection contained in $D^*$ has finitely
many actual $y$ values, even when its $x$ values are unbounded.
$\square$

**Lemma 6.6 (bounded discrepancy on every regular subset of $E^*$).**
For every regular $L\subseteq E^*$, the cost $c$ is bounded on $L$.

Proof. By Lemma 6.3 both coordinate projections $H_1=\pi_1(L)$ and
$H_2=\pi_2(L)$ are regular native languages contained in $D^*$.
Lemma 6.5 gives finite $Y_{H_1},Y_{H_2}$. Let $Y$ be their union and
form the finite native set

$$
S=\{U(y,y),U(F(y),y):y\in Y\}.
\tag{NIC.34}
$$

In every different-row pair at least one row has label $r_0$ or $r_1$,
since a pair with both rows $r_2$ is not different-row. That member of
the pair belongs to $S$, by the exact strata (NIC.32). This uses the
entire three-label relation, not its two special strata alone.

For a fixed finite native tree $s$ of height $H_s$, any different tree
$t$ has a disagreement at depth at most $H_s$. Indeed, agreement on
all labels at the reached nodes of $s$ would force the same branch
children and same terminal leaves in $t$, reconstructing $s$ completely
by finite induction. If replies agree through $H_s$, that reconstruction
applies and $t=s$, a contradiction. Therefore $\delta(s,t)\le H_s$.
Symmetry gives the same bound if $s$ is the second coordinate. The cost
on $L$ is consequently at most
$\max(\{0\}\cup\{H_s+1:s\in S\})$. If $L$ is empty this is a valid
vacuous bound. $\square$

**Lemma 6.7 (unbounded actual finite different-row pairs).** The function
$c$ is unbounded on $W$. Specifically, let

$$
y_0=\beta,\quad y_{n+1}=F(y_n),\quad
u_n^0=U(y_n,y_n),\quad u_n^1=U(y_{n+1},y_n).
\tag{NIC.35}
$$

Then both sources are finite members of the entire acquired $D^*$,
with exact rows $r_0,r_1$, and

$$
\delta(u_n^0,u_n^1)=n+1,\qquad
c(\operatorname{conv}(u_n^0,u_n^1))=n+2.
\tag{NIC.36}
$$

Proof. These are the actual finite sources of [NLC, (NLC.28)][NLC].
The first has $x=y_n$ and the second $x=F(y_n)$, so Lemma 6.5 gives
their exact labels and every retained acquired constraint with both
guards. The finite right combs $y_n,y_{n+1}$ agree at all depths less
than $n$ and first differ at $R^n$, where the first has $\beta$ and
the second a branch. Their first discrepancy depth is $n$. The two
$U$ sources differ only in their left subtrees and share their entire
right subtree. Prefixing the first discrepancy by $L$ gives depth
$n+1$ and no earlier discrepancy. This proves (NIC.36), which grows
without bound. The finite labels are never replaced by the equality
partition of an infinite limiting comb. $\square$

**Definition 6.8 (all-subsets boundedness equivalence and regular cuts).**
For $g:W\to\mathbb N\cup\{\infty\}$, say that $g$ is bounded on
$X\subseteq W$ when some finite $B\in\mathbb N$ satisfies
$g(w)\le B$ for every $w\in X$. Empty sets are bounded. Write

$$
f\approx c
\Longleftrightarrow
\forall X\subseteq W\quad
\bigl(c\text{ bounded on }X\ \Longleftrightarrow\
      f\text{ bounded on }X\bigr).
\tag{NIC.37}
$$

Both directions for every subset are required, as in [Vanden Boom,
§1.2][VB]. A regular finite sublevel cut means that
$\{w\in W:f(w)\le B\}$ is regular relative to $W$ for each finite
$B\in\mathbb N$. This is an explicit hypothesis on $f$, with no
association to a named automaton or cost framework assumed.

**Theorem 6.9 (B: obstruction with explicit regular-cut hypothesis).**
There exists no function $f:W\to\mathbb N\cup\{\infty\}$ such that
every finite sublevel cut of $f$ is regular relative to $W$ and
$f\approx c$ in the all-subsets sense of (NIC.37).

Proof. Suppose such an $f$ exists. On $O=W\setminus E^*$, $c$ is
identically zero. The direction from $c$-boundedness to $f$-boundedness
in (NIC.37), applied to this very subset $O$, gives a finite $B$ with
$f(w)\le B$ on all of $O$.

Let $T=\{w\in W:f(w)\le B\}$. It is regular relative to $W$ by
hypothesis and therefore a regular $\Gamma$ language, since $W$ is
regular. Its complement $L=W\setminus T$ is regular by Lemma 6.3.
No point of $O$ is in $L$, so $L\subseteq E^*$. Lemma 6.6 bounds
$c$ on $L$.

On $T$, $f$ is bounded by $B$. The reverse direction of (NIC.37), now
applied to the subset $T$, bounds $c$ on $T$. The union $W=T\cup L$
therefore has a finite $c$ bound, the maximum of these two bounds.
This contradicts Lemma 6.7. Values $\infty$ of $f$ cause no exception:
they belong to $L$, and the argument already covers $L$. No regularity
of $E^*$ or $O$ was assumed, and no imported theorem about threshold
cuts of a named cost model was used. $\square$

**Proposition 6.10 (inclusive prefix meaning and exact boundary).** For
the entire $D^*$ and its complete target $Q$,

$$
\operatorname{PrefDet}(D^*,Q,h)
\Longleftrightarrow
\forall w\in E^*,\quad c(w)\le h+1.
\tag{NIC.38}
$$

The obstruction in Theorem 6.9 concerns the raw canonical convolution
universe and the explicit two hypotheses in its statement. It makes
no claim against another encoding, constrained automata, costs defined
only on a promise domain, reductions preserving only global boundedness,
or decidability of Open problem 5.5.

Proof. For a different-row pair its sources are distinct, and (NIC.21)
is equivalent to $\delta(u,v)>h$. Prefix determination excludes all
such pairs. Thus it requires $\delta(u,v)\le h$ on every different-row
pair, which is exactly $c\le h+1$. This proves (NIC.38), including
$h=0$ and the absent-reply convention. In particular existence of a
determining depth is equivalent to boundedness of $c$ on $E^*$, and
also on $W$ since the remaining values are zero.

Theorem 6.9 uses the same raw universe for its regular cuts and for
both directions on *every* subset; its contradiction uses $O$ and
$T$ separately. Changing the encoding, removing $O$ through a promise,
or requiring only global boundedness does not provide those premises.
Consequently none of those distinct representation questions is answered
by this proof. Likewise $c$ counts a depth in the original finite source,
not the price of a legal action run. Its unboundedness and the exact
prefix meaning do not introduce a new coordinate-worst or weighted
service optimum. $\square$

## 7. Mathematical dependencies and remaining relation

**Definition 7.1 (source attributions).** The connected-sort and ambient
expansion argument in Lemmas 2.4–3.1 yields the all-source image theorem
3.2. Its native signed restriction is Theorem 3.3. The finite-row
consumer is the composition in Theorems 4.3 and 5.2. The regular-cut
boundary is Theorem 6.9. These are arguments within the native algebra
specified here; no global priority assertion is attached to them.

The normal bijection, atomic recurrence and forward translation are
reused from [ABC, §§2–4][ABC]. The exact finite branch factorization,
free-shape most-generality and scalar/block comparison forms are reused
from [NSF, §§2–3][NSF]. NSF's existential replacement witnesses are not
used as all-source representatives. Its fixed-navigation and guarded
compiler supplies the concrete original-prefix cases in Theorem 4.3.
[NPL, §5][NPL] supplies the complete finite row list, rather than a
runtime selector on an infinite source fiber. [URR, §§1–3][URR] is used
only at the proven Cartesian hypotheses in Proposition 3.5; its §7
retains the positive and reach-restriction boundary.

[ARH, §§1–3][ARH] supplies the paid acquired source interface and the
existing service/prefix existence bridge. Its Theorem 8.2 concerns
coordinate-preserving ordinary constructor equation/disequality cells,
whereas (NIC.12) retains interpreted $\rho$ and atomic rank parameters;
there is no conflict or reproof of that graph non-elimination theorem.
[NLC, §§8–9][NLC] supplies the entire $D^*$, all its labels and its
finite approximants. Its recurrent anchored-leaf limit can coalesce
finite equality partitions; the consumer here retains labels on finite
sources. Its supplied-context contact theorem and [CRF, Open problem
9.1][CRF] do not furnish a complete stopping rule for (NIC.22).
[NFO, §8][NFO] supplies prescribed-budget decisions and conditional
resource results, with its unrestricted existential stopping question
unchanged.

The free-shape unification ingredient is a free-term statement. The
free-term disunification arguments in [Comon–Lescanne, §3.2 and Appendix
B.3][CL], with their general-equational-theory boundary in §6.2, are not
assumed to apply to interpreted native feedback. The finite-tree
regularity operations in §6 are the ordinary determinization,
intersection and linear-image constructions of [TATA, §§1.1, 1.3–1.4][TATA].
The all-subsets convention alone is reused from [Vanden Boom, §1.2][VB];
no theorem from a named cost framework supplies a hypothesis of B.

**Open problem 7.2 (the original general action and resource question).**
For arbitrary nonempty complete signed fibers (NIC.17), decide whether
some inclusive original depth determines the entire $Q$ row, and obtain
the faithful arbitrary-finite-word legal service consequences under
Assumption 4.2. In the finite-image case, a terminating signed joint
choice in Open problem 5.5 would supply the determining depth or actual
finite counterpairs by Theorem 5.2. The image cover alone does not give
that choice. A proof must handle arbitrary positive interpreted
relations and all retained negative relations jointly, with authentic
finite-source row labels. Actual action/resource optimization still
requires its own entire-competitor correspondence and attainment
arguments, with (NIC.18)'s distinct objectives and zero weights.

## 8. References

[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NFO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_OBSTRUCTION.md
[CRF]: RECURSIVE_RELATIONAL_OBSERVATION_CONSTRUCTOR_RESOURCE_FRONTIER.md
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[TATA]: https://tata.gforge.inria.fr/
[VB]: https://www.cs.ox.ac.uk/people/michael.vandenboom/papers/thesis.pdf

**Reference 8.1 (native suppliers).** [ABC][ABC], *A canonical
atomic-block conjugacy*; [NSF][NSF], *Native signed feasibility*;
[NPL][NPL], *Native projection limitedness*; [URR][URR], *Uniform
residual realization*; [ARH][ARH], *Actually acquired mixed-epoch
relations and complete original recuts*; [NLC][NLC], *Native minimum
leaf depth and exact constructor-context contact*; [NFO][NFO], *Native
finite obstruction*; [CRF][CRF], *Constructor resource frontier*.
The cited numbered statements give their exact hypotheses above.

**Reference 8.2 (free terms).** Hubert Comon and Pierre Lescanne,
*Equational Problems and Disunification*, Journal of Symbolic Computation
7 (1989), 371–425. The cited free-term statements and their stated
equational-theory boundary support only the free-shape ingredient.

**Reference 8.3 (finite tree automata).** Hubert Comon, Max Dauchet,
Rémi Gilleron, Florent Jacquemard, Denis Lugiez, Christof Löding,
Sophie Tison and Marc Tommasi, *Tree Automata Techniques and
Applications*, 2008 edition, Chapter 1, especially Theorems 1.1.9 and
1.4.3 and §1.3. Determinization and linear images, including erasing
linear images, are the precise regular-language ingredients.

**Reference 8.4 (boundedness convention).** Michael Vanden Boom,
*Weak Cost Automata over Infinite Trees*, doctoral thesis,
University of Oxford, 2012, §1.2, pp. 6–7. The relation used here is
boundedness equivalence on every subset as defined in (NIC.37).

## 追加锚（本行以下为增补区）
