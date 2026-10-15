# Recursive relational observation: native overlap and closure boundaries

## 1. Native objects, observations and mathematical suppliers

**Definition 1.1 (the unchanged source and temporal observation).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad \operatorname{ht}(\alpha)=\operatorname{ht}(\beta)=0,
\qquad \operatorname{ht}(\langle u,v\rangle)
=1+\max\{\operatorname{ht}(u),\operatorname{ht}(v)\}.
$$

Pairing is free and ordered. Every finite word over $L,R$, including
$\varepsilon$, is a legal original-root literal. Its reply $r_t(a)$ is
in $\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$,
with absent after traversal passes a leaf. The homomorphic substitution is

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For every public integer $D\ge1$ retain exactly

$$
\mathcal F_D=\{\langle\alpha,v\rangle:\operatorname{ht}(v)\le D\},
\qquad W_D=\{q:|q|\le D-1\},
\qquad \mathcal P_D=\{Rq:q\in W_D\}.
\tag{OCB.1}
$$

One actual initial source remains stationary throughout preparation and
late acquisition. The iterates $\rho^kt$ specify prediction targets.

**Assumption 1.2 (complete paid export and late-target access).** A
single deterministic effective preparation begins source-blind from $D$
and common source-independent tables, receives no later request, and
terminates on every $t\in\mathcal F_D$. It acquires all source dependence
by charged original-root literal Reads. Its finite export $E(t)$ includes
every accessible surviving source distinction: selectors, control,
buffers, operands, lengths, allocation, handles, counters and accessible
timing. Every other accessible field is a function of this complete name
and public data. A separately paid handoff and access-isolation service
removes access to all other preparation dependence, including transcripts,
and supplies lawful common reader entry.

Only after export is a public source-independent $p\in\mathcal P_D$
supplied. The deterministic reader, from $E(t),D,p$ and common tables,
chooses zero Reads or one fresh Read of that same stationary $t$ at an
arbitrary finite original-root word. This choice precedes the reply and
every supplied count. Its final predictor must give

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad(t\in\mathcal F_D,\ p\in\mathcal P_D)
\tag{OCB.2}
$$

for every subsequently supplied authentic $k\ge0$, without further
Reads. Define $M_1(D)=\min|E[\mathcal F_D]|$ over these jointly correct
procedures. There is no subtree, equality, source-identity, age, reset,
copying, free-navigation or advice port. Handoff, isolation, continuity,
entry and authentication are service premises. Preparation Reads,
work/control, temporary storage, installed tables, post-request workspace,
final predictor size, submitted address lengths and letters, authentic
count representation and physical time are separate resource coordinates.
This is the original interface of [FMR, §§1–2][FMR] and [NPC, §1][NPC].

**Definition 1.3 (credited finite native interface).** Put

$$
C_0=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C_0\},\qquad
S_{d+1}=\{\alpha,\beta\}\sqcup\{\langle u,v\rangle:u,v\in S_d\}.
\tag{OCB.3}
$$

For $q\in W_d$ write $g_q(u)=\Gamma_q(u)$ and $r_q(u)=r_u(q)$.
Use the full temporal factor of [AAR, §§12–13][AAR]. If $q$ ends at
an original branch, $\Gamma_q(u)=(0,0)$. Otherwise let its first
original leaf have label $\ell$ at $a$, write $q=ar$, put
$e(\alpha)=0,e(\beta)=1$ and $s(r)=\#L(r)+2\#R(r)$, and set

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{OCB.4}
$$

On attained $(b,c)$ the credited decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1,\ k=b-1,\\
\alpha,&c=1,\ k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{OCB.5}
$$

It equals $r_{\rho^ku}(q)$ for all $k\ge0$. Conversely the complete
trajectory recovers $b$ as the first branch count and $c$ by the
occurrence of an alpha stage. Write $h(z)=\operatorname{Pred}(z,0)$
and $G_q=\Gamma_q[S_d]$. The completion $\pi_d(v)\in S_d$ preserves
all $W_d$ replies and factors and fixes $S_d$. On a canonical block,
a length-$d$ literal is alpha exactly when its parent is branch and
is absent otherwise; longer literals are absent. Thus every finite
canonical experiment is a function of one boundary reply in the same
queried block or a constant. These are [FMR, Lemma 2.2][FMR]'s facts;
no target-prefix restriction is imposed on readers.

A complete native template on $n$ blocks chooses, for every $(i,q)$,
either $g_q(x_i)=\zeta\in G_q$ or

$$
g_q(x_i)=\delta_{i,q}(r_a(x_j)),\qquad
j\in[n],\ a\in W_d,\quad\delta_{i,q}:\mathcal A\to G_q.
\tag{OCB.6}
$$

Let $C_\Theta\subseteq S_d^n$ be its simultaneous solution set.
All references name the same tuple. Arbitrary donors, cycles, self
queries, off-target queries and correlations are retained. A nonempty
subset is admissible if it has these witnesses, without requiring it
to equal their complete solution set. [NDR, Theorem 2.2][NDR] permits
saturation without changing cover optima or nonnegative mass maxima.
For arbitrary nonnegative whole-block weights define

$$
\Omega_{\boldsymbol w}(B)=\sum_{x\in B}\prod_iw_i(x_i),\qquad
\beta_d(w)=\sup_{n\ge1}\max_\Theta
                  \Omega_{(w,\ldots,w)}(C_\Theta)^{1/n}.
\tag{OCB.7}
$$

Every $w_i$ is used once with its entire joint scope.

**Assumption 1.4 (credited correspondences and rate suppliers).** The
native sources cited here are their committed mathematical statements
at revision `f586077f0b16eb03fc18e753a30e4b6b68996dae`.
[RRN, Theorems 4.2, 5.2 and 6.1][RRN] give a same-solution
representative-reply normalization and its two-way owned-seed language.
In that language each seed $s_c$ has domain $T_c\subseteq\mathcal A$
and a distinct actual owner port $o_c$. Each port prescribes a constant
in $G_q$ or $z_{i,q}(s)=B_{i,q}(s_c)\in G_q$. At its owner,

$$
h(B_{o_c}(a))=a\qquad(a\in T_c).
\tag{OCB.8}
$$

Repeated seed occurrences remain the same variable. A seed assignment
is realizable precisely when each prescribed full factor vector is
that of an actual block $x_i(s)\in S_d$, necessarily unique. Its local
potential is zero if reconstruction fails and otherwise
$\Phi_i(s)=w_i(x_i(s))$. RRN gives the bijection and identity

$$
Z(\mathcal N;\boldsymbol w)=\sum_{s\in\prod_cT_c}\prod_i\Phi_i(s)
=\Omega_{\boldsymbol w}(C_\Theta).
\tag{OCB.9}
$$

[CBN, Theorems 2.2, 4.2 and 6.2][CBN] supply actual constructor
reconstruction and its equality-aware representation with these same
once-owned weights. Neither supplier factors an arbitrary joint weight.
A general nonnegative $W(x_1,\ldots,x_n)$ is also transported by the
same bijection, without replacing it by a product.

Writing $K_d(n)$ for the unrestricted admissible cover number,
[FMR, §§3 and 6][FMR] and [NPC, §§5–7][NPC] supply

$$
\begin{aligned}
\sigma_d&=\inf_{n\ge1}n^{-1}\log_2K_d(n),
&2^{-\sigma_d}&=\min_{\mu\in\Delta(S_d)}\beta_d(\mu),\\
\lambda&=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
       =\sup_d2^{-d}\sigma_d,
&0&\le\lambda-2^{-d}\sigma_d\le2^{-d}\phi,
\end{aligned}
\tag{OCB.10}
$$

where $U_0=1$, $U_{h+1}=1+U_h^2$ and
$\phi=\lim_h2^{-h}\log_2U_h\le1$. A probability cap
$\beta_d(\mu)\le C$ gives

$$
M_1(D)\ge\left\lceil C^{-2^{D-d}}\right\rceil\quad(D\ge d),
\qquad\lambda\ge-2^{-d}\log_2C.
\tag{OCB.11}
$$

All logarithms and finite entropies below have base two. These suppliers
and the mature finite entropy, rectangular-relation, sum-product and
linear-programming ingredients are credited within the proofs. The new
native deductions carry ordinary proofs here; no kernel verification or
worldwide novelty is asserted.

## 2. Exact adjacent temporal compatibility

**Definition 2.1 (unary temporal summaries).** Put

$$
Q_0=\{(0,0),(2,1),(1,0)\},\qquad \ell_L=1,\quad\ell_R=2,
$$

and, for an attained factor $z=(b,c)$, define

$$
U(z)=\begin{cases}\star,&z=(0,0),\\b,&\text{otherwise},\end{cases}
\qquad
D_e(z)=\begin{cases}\star,&z\in Q_0,\\b-\ell_e,&z\notin Q_0.
\end{cases}
\tag{OCB.12}
$$

The formal label $\star$ is distinct from every integer. All port
prescriptions still take values in their actual $G_q$ and retain their
owner domains and guards.

**Theorem 2.2 (exact compatibility by temporal-summary equalities).**
For every $d,n\ge1$ and every owned-seed network of Assumption 1.4,
a seed assignment is realizable if and only if

$$
U(z_{i,q}(s))=D_e(z_{i,qe}(s))
\quad(i\in[n],\ q,qe\in W_d,\ e\in\{L,R\}).
\tag{OCB.13}
$$

There are $n(2^d-2)$ adjacent tests before removal of tautologies or
redundancies, including zero at $d=1$. Each test is constant, unary,
or a binary relation of the form $f(s_c)=g(s_b)$. On distinct seeds
this is rectangular: its nonempty components are products of fibers
of the two unary maps, with at most four attained labels on each side.
It introduces neither auxiliary variables nor independent copies.

Proof. At a branch endpoint $q$, its child $qe$ is initially present,
so its factor is in $Q_0$. At any nonbranch factor $(b,c)$,
extending the blocked path by $e$ gives

$$
\Gamma_{qe}=(b+\ell_e,\mathbf1_{e=R}).
\tag{OCB.14}
$$

This follows directly from (OCB.4), including when $q$ is itself the
original leaf. An initially absent child has second coordinate fixed
by its last letter $e$ and cannot have a factor in $Q_0$.
Consequently (OCB.13) is exactly the branch/present-child alternative
or rule (OCB.14); it does not drop a free second-coordinate choice.
The attained-range premise at $qe$ already fixes that coordinate.

The root factor lies in $G_\varepsilon=Q_0$. Its $h$-image is
nonabsent. Passing $h$ through the adjacent rules gives exactly the
legal constructor-parent constraints: a branch has nonabsent children,
and a leaf or absent port has absent children. Thus the prescribed
replies reconstruct one canonical tree per block by CBN Theorem 2.2.
At each present endpoint its factor is its unique value in $Q_0$.
Induction along every path beyond a blocking leaf, using (OCB.14),
then proves that every prescribed full factor equals that tree's
actual $\Gamma$. A branch at the cutoff is completed by $C_0$.
This proves sufficiency; the same local rules prove necessity.
It also proves the assertion for constant prescriptions and the
empty product of seeds. An empty domain gives no assignment on
either side of the equivalence.

The complete binary rooted menu has $2^d-1$ vertices and $2^d-2$
edges. Pulling an equality of labels back through two unary seed
maps gives the disjoint union
$\bigcup_a f^{-1}(a)\times g^{-1}(a)$. This is the usual rectangular
relation of [Dyer–Richerby, §3, Lemma 1][DR]. If both expressions use
the same seed they are substituted on that same value and give a
unary condition. $\square$

**Theorem 2.3 (exact weighted carrier in both native directions).**
Let $\mathcal E$ be the equalities (OCB.13). Define a total public
reconstruction $\bar x_i(s)$ from the prescribed reply array: use its
CBN inverse when legal and use $\alpha$ otherwise. Then

$$
\Omega_{\boldsymbol w}(C_\Theta)
=\sum_{s\in\prod_cT_c}
       \left(\prod_{a\in\mathcal E}\mathbf1_a(s)\right)
       \prod_iw_i(\bar x_i(s)).
\tag{OCB.15}
$$

Every complete native template has this representation, and every such
representation carrying the actual owner ports, ranges, domains and
prescription tables of RRN gives a complete original template with this
same identity. The number $n$ of original potential owners is unchanged.
For an arbitrary correlated nonnegative $W$, replace the last product
by $W(\bar x_1(s),\ldots,\bar x_n(s))$.

Proof. Theorem 2.2 makes the indicator product exactly the original
realizability indicator. On it the actual reconstruction is unique.
The owner identity (OCB.8) recovers each seed as its actual owner reply,
so each original solution has exactly one lift. Off it the assigned
value of $\bar x_i$ is immaterial. Apply both directions of RRN
Theorem 5.2 to obtain (OCB.15), including zero weights and empty
solution sets. The same bijection proves the assertion for $W$.
Thus both pressure inequalities are identities for each finite network,
not comparisons only at a selected optimizer. Arbitrary rectangular
constraint systems lacking this native provenance are not substituted
for the quantified class. $\square$

**Theorem 2.4 (expression-forest thinning and its exact limit).** Form
an expression vertex for each unary function of a declared seed appearing
in (OCB.13). Identify two vertices only if they are functions of the
same seed agreeing pointwise on its domain, or are the same constant
value. Draw one edge for each equality. Replacing each connected
component by any spanning tree preserves all feasible seed assignments,
actual tuples and every weighted mass (OCB.15), with $n$ unchanged.
Different functions of one seed retain their common argument.

For every $n\ge2$ there is an actual depth-two network whose
nontrivial equalities form a cycle, for which a spanning tree suffices
but deletion of any tree bridge changes the solution set.

Proof. For any fixed seed assignment, equality on a tree makes all
expression values in its component equal, and hence implies each
removed edge. The converse follows because tree edges were original
edges. Functions remain evaluated on the original shared seeds;
transitivity does not make two different functions of that seed equal.
Substitution in (OCB.15) proves every mass assertion.

For the sharpness assertion let $s_i\in\{\alpha,\beta\}$ be owned
at block $i$'s root. Prescribe the root factor of $s_i$, the $L$ factor
of $s_{i+1}$, and the $R$ factor of $s_i$, with indices modulo $n$.
These are actual attained tables, with root guards excluding branch.
The only nontrivial adjacent conditions say $s_i=s_{i+1}$; hence the
full solutions are the two constant leaf tuples. If a retained set
of equality edges has components $\mathcal C$, the relaxed seed
relation, mapped to its actual root-leaf tuples, has mass exactly

$$
\prod_{C\in\mathcal C}
 \left(\prod_{i\in C}w_i(\alpha)+\prod_{i\in C}w_i(\beta)\right).
\tag{OCB.16}
$$

Indeed one leaf label may be chosen independently per component,
and the original block weights multiply on each choice. Unit weights
give $2^{|\mathcal C|}$. A cycle edge is redundant, while deleting a
tree bridge increases this number from two to four. This is a statement
about these actual finite networks, not their optimality for pressure.
$\square$

**Theorem 2.5 (when an owned weight argument can be removed).** Fix
a feasible seed relation $R$ and a block $i$, with seed scope $I_i$.
For $c\in I_i$, the value $w_i(x_i(s))$ can be written on all of $R$
as a function of $s|_{I_i\setminus\{c\}}$ exactly when it is constant
on each fiber of that restricted projection. Such a rewriting works
for every nonnegative $w_i:S_d\to[0,\infty)$ exactly when $x_i(s)$
itself is constant on each such fiber. In particular a realized
change of an actual owner reply in block $i$, with the other scoped
seeds fixed, prevents universal removal of that argument.

Proof. A factored function is constant on projection fibers. Conversely
assign the common value to every attained projected tuple, extending
arbitrarily off its image. For the universal claim, two different actual
blocks are separated by the indicator weight of either one. An owner
reply is an actual reply of its block, so changing it changes the block.
Empty relations satisfy the statements vacuously. This is a finite
pointwise criterion; equality of one total sum is insufficient.
$\square$

## 3. Actual native failure of rectangular projection closure

**Definition 3.1 (the exact-elimination class).** A rectangular-only
elimination step removes a seed and replaces its incident constraints
and owned weight by a product of unary factors and binary factors with
rectangular support on the existing remaining variables. It introduces
no auxiliary variable and retains no general joint potential. Exactness
requires equality for every remaining assignment, not just one scalar
sum. Ordinary elimination with an arbitrary joint factor is outside
this restricted class.

**Theorem 3.2 (three native blocks with NAND projection).** At depth
two write $A=\alpha$, $B=\beta$, $C_0=\langle A,A\rangle$.
A selector $c\in\{0,1,2\}$ is the actual root reply at an owner block,
represented respectively by $u_c=A,B,C_0$. Let $x,y\in\{A,B\}$
be actual root replies at two further owner blocks. Put

$$
(f(0),f(1),f(2))=(A,A,B),\qquad
(g(0),g(1),g(2))=(A,B,A).
\tag{OCB.17}
$$

Prescribe all factors of block zero from $u_c$. In block one prescribe
$\Gamma_\varepsilon(x),\Gamma_L(f(c)),\Gamma_R(x)$, and in block
two prescribe $\Gamma_\varepsilon(y),\Gamma_L(g(c)),\Gamma_R(y)$.
These are legal RRN data, with complete native solution set

$$
\{(A,A,A),(B,A,B),(C_0,B,A)\}\subseteq S_2^3.
\tag{OCB.18}
$$

Eliminating $c$ gives exactly the Boolean NAND support
$\{(A,A),(A,B),(B,A)\}$. If its three owner-block weights are
$a,b,c_0>0$ and the two visible block weights are one, its exact
eliminated potential, in the order $A,B$, is

$$
\begin{pmatrix}a&b\\c_0&0\end{pmatrix}.
\tag{OCB.19}
$$

No rectangular-only exact step of Definition 3.1 represents this result.

Proof. Selector and leaf domains are enforced by their actual root
owner equations and the RRN off-domain guards. All prescribed factors
lie in the required attained $G_q$. A leaf $A$ has $L$ factor $(3,0)$,
a leaf $B$ has $L$ factor $(2,0)$; their $R$ factors are $(4,1)$ and
$(3,1)$. The leaf guards make blocks one and two actual leaves. Their
$L$ equations impose exactly $x=f(c)$ and $y=g(c)$. All their other
factors then agree, and block zero is uniquely $A,B,C_0$ as specified.
This proves (OCB.18) and one lift per visible pair. Each primitive
relation $f(c)=x$ or $g(c)=y$ is rectangular.

The projection has three corners of a square and lacks $(B,B)$, so
is not rectangular. Summing the selector weight once gives (OCB.19).
The support of a product of nonnegative factors is the intersection
of their supports. Intersections of rectangular binary relations,
their transposes, and unary restrictions on two variables are
rectangular. They cannot give this support. In particular rectangular
completion would change the unit mass from three to four. General
binary elimination can simply retain (OCB.19), with no contradiction.
This is the distinction between rectangular primitives and the
primitive-positive closure required in [Dyer–Richerby, §§3–4][DR].
$\square$

**Theorem 3.3 (positive exact-one-in-three formulas have unique native
lifts).** Let a formula have $v$ Boolean variables and $m$ ordered
clauses, each containing three distinct variables with no negations.
For $N=v+4m\ge1$ there is a complete depth-two native template on
exactly $N$ original blocks whose actual solutions are in bijection
with satisfying assignments. Every satisfying assignment has exactly
one native lift. Variable sharing across arbitrarily many clauses is
allowed. Every original block weight remains once in the corresponding
weighted sum. In particular, for the uniform probability on all eleven
states of $S_2$, its mass is

$$
\frac{\#\{\text{satisfying assignments}\}}{11^{v+4m}}.
\tag{OCB.20}
$$

Proof. Give each variable a leaf-owner block, with its three factors
prescribed from its own root leaf seed. Give each clause a selector-owner
block with states $A,B,C_0$ and all factors prescribed by its root seed;
interpret selector value $k\in\{0,1,2\}$ as its true position.
For each of its three occurrences of variable $x_l$, add one connector
block with factors

$$
\Gamma_\varepsilon(x_l),\qquad
\Gamma_L\bigl(B\text{ if }c_j=k\text{, else }A\bigr),\qquad
\Gamma_R(x_l).
\tag{OCB.21}
$$

The connector root is prescribed from the actual variable-owner reply;
it creates no new seed or observation. Every connector factor is a
constant or a function of one actual owner-root reply and lies in the
appropriate attained range. Theorem 2.2, or the leaf calculation in
Theorem 3.2, says precisely that this connector exists if and only if
$x_l=B$ exactly at its clause's selected position. Thus any native
solution gives a satisfying Boolean assignment. Conversely a satisfying
assignment determines one selector in every clause and every connector
leaf uniquely; these choices satisfy all factors. There are $v$ variable,
$m$ selector and $3m$ connector blocks, proving the exact exponent.
No variable occurrence is an independent copy of its owner. The same
bijection proves the weighted assertion and (OCB.20).

If $m=0$, the $v$ unconstrained leaf owners give all $2^v$ assignments.
The degenerate $v=m=0$ has the single empty assignment and empty product
mass one; its actual-source realization can use one fixed padding block.
An unsatisfiable formula gives an empty native solution set.

The locally identifiable support $\{A,B,C_0\}$ itself is admissible:
its root reply identifies its state, so its full Cartesian powers are
admissible. A probability supported there therefore has $\beta_2=1$.
Consequently this exact finite representation and the obstruction in
Theorem 3.2 imply no unrestricted pressure-hardness, optimized-capacity
or noncomputability conclusion. The credited full depth-two pressure
optimization remains [NCM, Theorem 4.1][NCM]. $\square$

**Theorem 3.4 (paid full-family realization of the displayed fibers).**
Let $B\subseteq S_d^N$ be any nonempty finite admissible relation,
with $N\ge1$, including Theorems 2.4, 3.2 and 3.3's nonempty
solution sets. Put $H=\lceil\log_2N\rceil$, $k=2^H$, pad the tuple
by $k-N$ fixed $\alpha$ blocks, and put $D=d+H$. There is a correct
full-family preparation and reader satisfying Assumption 1.2, with
complete attained alphabet exactly

$$
|S_D|-|B|+1.
\tag{OCB.22}
$$

It merges exactly the padded perfect-scaffold image of $B$ among the
canonical states and gives each other canonical state its own name.
On every original source it uses

$$
T_{\rm prep}=2^D-1,\qquad Q_{\rm prep}\le D,\qquad
A_{\rm prep}=(D-1)2^D+1.
\tag{OCB.23}
$$

If $B$ is empty, use $|S_D|$ singleton canonical names instead.

Proof. Let $T_H$ be the fixed ordered perfect scaffold with these $k$
actual frontier blocks. It is injective on their tuples and lies in
$S_D$. Before any request, actually Read every $Rq$, $q\in W_D$,
including absent replies, on the same stationary source. These charged
replies determine $\pi_D(v)$ by FMR. Its public finite membership table
selects the stated name. Exactly $|B|$ canonical states share the merged
name, proving (OCB.22); every name is attained by a canonical source.
Public scan order, fixed-width naming, public allocation and padded
finite table computation, followed by the paid isolation of Assumption
1.2, leave only that complete name accessible. The counts are
$\sum_{l<D}2^l=2^D-1$ and
$\sum_{l<D}(l+1)2^l=(D-1)2^D+1$.

A singleton canonical name fixes every factor and needs zero Reads.
At the merged name, targets above the cut have constant branch factor;
padding-block targets have their public fixed factors. Every other
target is $Ra_iq$, $q\in W_d$, at an actual frontier occurrence.
Its admissibility witness queries at most one original-root literal
$Ra_ja$, $a\in W_d$, of length at most $1+H+d-1=D$.
For the selector constructions the donor may simply be the specified
owner-root word $Ra_j$, of length $H+1$. No subtree is passed to the
reader. Pairing homomorphism at these actually present occurrences gives

$$
r_{\rho^kt}(Ra_iq)=r_{\rho^k(t|_{Ra_i})}(q).
\tag{OCB.24}
$$

This is exactly `original_present_transport`'s presence premise in
[NativeDepthPatterns][D5N]. On every variable-shaped source with the
same canonical name, $\pi_D$ preserves both the selected boundary reply
and the target factor. Thus the installed factor table and (OCB.5)
answer every subsequent authentic count, with the literal chosen before
that count. All permitted targets, including absent ones, are covered.

The acquired boundary, membership workspace and preparation transcript
are isolated, rather than exported as seeds, source identity or a cut
descriptor. Table generation/installation, work/control, temporary
buffers, post-request workspace, address construction, authentic count,
predictor size, entry, authentication and physical time remain separate
resources. The predictor $(b,c)$ needs at most
$\lceil\log_2(2D+1)\rceil+1$ bits separately. These deliberately
nonoptimal codes do not determine $M_1(D)$ and do not preserve an old
preparation cost. The scan bounds are the credited FMR bounds; the
fiber sets and their exact counted use here are the stated native
constructions. $\square$

## 4. The exact owner-only proportional envelope

**Definition 4.1 (local owner domination).** In an arbitrary RRN network,
let $O_i$ contain all seeds whose owner port is in original block $i$,
and let $I_i$ contain the other seeds appearing in its factor prescriptions.
The $O_i$ partition all seeds; incoming seed sets can overlap arbitrarily.
Write the actual local potential as $\Phi_i(a,b)$, where $a$ is the
entire owned tuple and $b$ is the incoming tuple. No factorization within
either tuple is required. A local fragment $\eta$ consists of these
one-block tables, domains and designated actual owner ports, allowing
completion by additional actual donor blocks. For nonempty domains put

$$
M_\eta(a)=\max_b\Phi_\eta(a,b),\qquad
L_\eta(w)=\sum_a M_\eta(a).
\tag{OCB.25}
$$

An empty owner set has one empty tuple. A network with any empty seed
domain has zero mass and is treated directly, without a probability on
an empty domain. Owner-only proportional domination means a joint
probability $\pi_\eta$ on the whole owned tuple with

$$
\Phi_\eta(a,b)\le K\pi_\eta(a)\quad\text{for every }a,b.
\tag{OCB.26}
$$

This relaxation maximizes incoming values separately at different blocks;
it does not assert that those maximizing choices are jointly realizable.

**Definition 4.2 (reply-basis test supports).** For nonempty
$P\subseteq S_d$ let

$$
E(P)=\{q\in W_d:g_q\text{ is a function of }r_q\text{ on }P\},
\qquad v_P(u)=(r_q(u))_{q\in E(P)}.
\tag{OCB.27}
$$

Let $\mathscr R_d$ contain the nonempty $P$ with
$|g_q(P)|\le4$ for every $q$ and $v_P$ injective on $P$. Define

$$
\mathcal U_d(w)=\max_{P\in\mathscr R_d}\sum_{u\in P}w(u),
\qquad \mathcal U_d(0)=0.
\tag{OCB.28}
$$

The test family is hereditary: on restriction, target ranges shrink,
$E(P)$ can only grow, and its old separating replies remain separating.
It contains every singleton. Its members are analytical test supports;
they are not all asserted to be admissible native code fibers.

**Theorem 4.3 (optimal local domination and its all-network bound).**
For every nonnegative whole-block weight and every local fragment with
nonempty domains, the least $K$ in (OCB.26) is exactly $L_\eta(w)$.
Moreover, for every $d,n$, every actual owned-seed network and arbitrary
nonnegative $w_i$,

$$
Z(\mathcal N;\boldsymbol w)
\le\prod_i L_{\eta_i}(w_i)
\le\prod_i\mathcal U_d(w_i),
\qquad \beta_d(w)\le\mathcal U_d(w).
\tag{OCB.29}
$$

The universal one-block envelope is exact:

$$
\max_\eta L_\eta(w)=\mathcal U_d(w),
\tag{OCB.30}
$$

where fragments may have actual outside owners supplied in a finite
completion. The completion's additional blocks remain charged original
blocks; (OCB.30) does not assert that all one-block maximizing choices
coexist in a fixed network.

For a positive network mass $Z$ define its actual seed law
$Q(s)=Z^{-1}\prod_i\Phi_i(s)$ on the positive-mass realizable
assignments. Put $L_i=L_{\eta_i}(w_i)$ and
$q_i=\mathcal L_Q(s_{O_i})$. Then the exact defect of this domination is

$$
\begin{aligned}
\log_2 Z
={}&\sum_i\log_2L_i-\operatorname{TC}_Q(s_{O_1},\ldots,s_{O_n})\\
&-\sum_iD_2\left(q_i\middle\|M_{\eta_i}/L_i\right)
 -\sum_i\mathbb E_Q\log_2
       \frac{M_{\eta_i}(s_{O_i})}{\Phi_i(s)}.
\end{aligned}
\tag{OCB.31}
$$

Here $\operatorname{TC}(Y_1,\ldots,Y_n)=\sum_iH(Y_i)-H(Y)$.
Every displayed defect is nonnegative and every logarithm is taken
only on positive $Q$ support. If $Z=0$, (OCB.29) already applies
without such a law. The same identity holds on any retained subrelation
of the realizable seed assignments, with $Z$ and $Q$ restricted to that
subrelation and the same local maxima $M_{\eta_i}$. It does not replace
the subrelation by its witness completion.

Proof. Any (OCB.26) gives $M_\eta(a)\le K\pi_\eta(a)$;
summing yields $L_\eta\le K$. If $L_\eta>0$, the choice
$\pi_\eta=M_\eta/L_\eta$ attains equality. If $L_\eta=0$,
any probability on the nonempty owned product works at $K=0$.
This is elementary finite probability domination, used here with all
of a block's owned variables jointly.

Multiply the pointwise dominations and sum on the same original seed
assignment. Because the $O_i$ partition all seeds,

$$
\sum_s\prod_i\pi_i(s_{O_i})=\prod_i\sum_{s_{O_i}}\pi_i(s_{O_i})=1.
$$

This proves the first inequality in (OCB.29). The product probabilities
are a dominating measure, not the actual seed law. No shared incoming
seed was copied or chosen independently in the actual network.

For every owned tuple $a$ with $M_\eta(a)>0$, select one maximizing
incoming tuple and its actual reconstructed block $u_a$. Different
owned tuples give different blocks because each owned coordinate is
its actual owner reply. Their set $P$ is range-feasible: each prescribed
target is constant or has at most four seed values. At each owner $q$,
$g_q(u_a)=B_q(r_q(u_a))$, so $q\in E(P)$, and these owned replies
separate all $u_a$. Thus $P\in\mathscr R_d$ and
$L_\eta(w)=\sum_aw(u_a)\le\mathcal U_d(w)$. If no positive maximum
exists the inequality is immediate. RRN's exact correspondence now
proves the all-template pressure cap, with no restriction on topology,
correlations, repeated seeds or zeros.

For the reverse envelope inequality choose a maximizing
$P\in\mathscr R_d$. Put a distinct owned seed at every $q\in E(P)$,
with domain $r_q(P)$ and table decoding $g_q$ from that same reply.
At each other target use a separate incoming seed to encode its at-most-four
factor values. Each $u\in P$ has a compatible local assignment;
its owned tuple is unique to $u$. Therefore $L_\eta(w)\ge w(P)$.
All such incoming seeds have genuine outside owners. For $d\ge2$,
the four actual trees

$$
\alpha,\quad\langle\alpha,\alpha\rangle,\quad
\langle\beta,\alpha\rangle,\quad\langle C_0,\alpha\rangle
\tag{OCB.32}
$$

belong to $S_d$ and have respectively absent, alpha, beta and branch
at $L$. A subset realizes any required incoming domain, with every
target in that donor block decoded from this identifying actual $L$
owner. Use a separate such block for each incoming seed and retain its
weight once. At $d=1$ the three root states suffice, and the root is
already self-decodable on every test support. Extending unused table
entries with RRN's actual guards completes these fragments legally.
Together with the proved upper this establishes (OCB.30).

For (OCB.31), the owner groups partition the full seed tuple, so
$H_Q(s)=\sum_iH(q_i)-\operatorname{TC}_Q(O)$. The definition of $Q$
gives $\log_2Z=H_Q(s)+\sum_i\mathbb E_Q\log_2\Phi_i(s)$.
For each $i$ use the elementary relative-entropy identity

$$
H(q_i)+\mathbb E_Q\log_2\Phi_i(s)
=\log_2L_i-D_2(q_i\|M_{\eta_i}/L_i)
 -\mathbb E_Q\log_2\frac{M_{\eta_i}(s_{O_i})}{\Phi_i(s)}.
$$

Sum these equalities. For a retained subrelation use its restricted
normalized law in the same identities; its owner map remains injective
and it is never replaced by its completion. The ratio is at least one,
and the other two defects are the usual finite entropy defects. These mature common-law
identities, as in [Madiman–Tetali][MT], serve here to quantify exactly
the lost compatibility in the native domination (OCB.29); they are not
additional standalone entropy results. $\square$

**Theorem 4.4 (finite optimization and the identical transversal
formulation).** Let $z_{\rm own}(d)$ be the fractional set-cover optimum
of $S_d$ by $\mathscr R_d$. Then

$$
\min_{\mu\in\Delta(S_d)}\mathcal U_d(\mu)=z_{\rm own}(d)^{-1},
\tag{OCB.33}
$$

and consequently

$$
\sigma_d\ge\log_2z_{\rm own}(d),\qquad
M_1(D)\ge\left\lceil z_{\rm own}(d)^{2^{D-d}}\right\rceil,
\qquad \lambda\ge2^{-d}\log_2z_{\rm own}(d).
\tag{OCB.34}
$$

The alternative finite owner-transversal expression

$$
\max_{\substack{\varnothing\ne P\subseteq S_d\\
                         |g_q(P)|\le4\ (q\in W_d)}}
 \sum_{y\in v_P(P)}\max_{u\in P:v_P(u)=y}w(u)
\tag{OCB.35}
$$

is exactly $\mathcal U_d(w)$, not a distinct cap mechanism.

Proof. Finite set-cover linear-programming duality gives nonnegative
weights $a$ of maximum total $z_{\rm own}(d)$ subject to
$a(P)\le1$ for every $P\in\mathscr R_d$. Singletons guarantee finite
coverage and a positive finite optimum. For any probability $\mu$,
the vector $\mu/\mathcal U_d(\mu)$ is dual feasible, so
$1/\mathcal U_d(\mu)\le z_{\rm own}(d)$. Conversely normalize an
optimal dual of total $z_{\rm own}(d)$ to a probability; its
$\mathcal U$ is at most the reciprocal. This proves equality, and
rational LP data give a rational attaining vector. Theorem 4.3 and
the credited (OCB.10)–(OCB.11) imply (OCB.34).
These auxiliary fractional cover members are test sets, not native upper
code constructions. Their dual yields lower bounds against all original
competitors.

To prove (OCB.35), in each nonempty $v_P$ cell choose a maximizing
state and let $Q$ be the chosen set. The old $E(P)$ remains
self-decodable on $Q$ and separates its chosen states, so
$Q\in\mathscr R_d$. Its mass is the sum in (OCB.35), proving that
expression is at most $\mathcal U$. A reply-basis test set has only
singleton cells, giving the reverse inequality. Thus separate use of
the transversal description supplies no additional pressure bound.
$\square$

## 5. Product grouping, stability and the exact local-language boundary

**Definition 5.1 (paired interfaces and the specified rule class).** A
finite paired interface has finite states and paired maps $(g_q,r_q)$
with each reply alphabet of size at most four, together with constants.
Define $E(P)$, $\mathscr R_I$ and $\mathcal U_I$ as in Definition 4.2,
using the designated reply paired with each target. A product of such
interfaces has constituent pairs $(g_{j,q}(x_j),r_{j,q}(x_j))$.
One port returns one constituent reply, never a reply vector. Test
supports in the product may be arbitrarily correlated.

A finite $V_{\rm own}$ derivation has rational labels $(d,\mu,C)$,
with $\mu$ on the entire $S_d$ and $C>0$. Its only rules are:

1. The exhaustive owner-proportional leaf, testing
   $C\ge\mathcal U_d(\mu)$; equivalently it checks the complete
   finite envelope of Theorem 4.3.
2. An arbitrary finite product-grouped leaf, for any $m\ge1$, testing
   $C^m\ge\mathcal U_{I_d^{\times m}}(\mu^{\otimes m})$ on every
   product test support. Groupings can be nested and parenthesized
   arbitrarily.
3. The actual scaffold rule: from $(d_0,\nu,C_0)$ and $h\ge0$,
   conclude $(d_0+h,\nu^\uparrow,C)$ if $C\ge C_0^{2^h}$, where
   $\nu^\uparrow(T_h(x))=\prod_{j=1}^{2^h}\nu(x_j)$ and is zero
   off the actual perfect-scaffold image.
4. The probability-stability rule: from $(d,\nu,C_0)$ conclude
   $(d,\mu,C)$ if $C\ge C_0+\operatorname{TV}(\mu,\nu)$.

Every rule retains all supports and zeros. The last two are exactly the
corresponding [JTC, Definition 9.1][JTC] rules. Product grouping here
means product interfaces and these owner-only leaves; it does not add an
arbitrary exact joint calculation across a cluster of original owner
blocks. A rule retaining such a joint relation is outside this specified
class and remains available as a different method.

**Theorem 5.2 (complete acceptance boundary, with all grouped supports).**
For finite paired interfaces and arbitrary nonnegative weights,

$$
\mathcal U_{\prod_{j=1}^m I_j}(\bigotimes_jw_j)
       =\prod_{j=1}^m\mathcal U_{I_j}(w_j).
\tag{OCB.36}
$$

In particular

$$
\mathcal U_{d+h}(w^\uparrow)=\mathcal U_d(w)^{2^h},\qquad
|\mathcal U_d(\mu)-\mathcal U_d(\nu)|
       \le\operatorname{TV}(\mu,\nu).
\tag{OCB.37}
$$

For every rational input, finite acceptance by precisely $V_{\rm own}$
is equivalent to $C\ge\mathcal U_d(\mu)$. The predicate is total
computable and sound at every length for all complete native templates.

Proof. Take a correlated product test support $P$, and write
$P_j=\pi_jP$. Self-decodability of a designated pair in constituent
$j$ is equivalent to its self-decodability on $P_j$. Let
$v_j(x_j)=(r_q(x_j))_{q\in E(P_j)}$. The tuple of these vectors
separates $P$. Therefore

$$
\sum_{x\in P}\prod_jw_j(x_j)
\le\prod_j\left[
 \sum_y\max_{u\in P_j:v_j(u)=y}w_j(u)\right].
\tag{OCB.38}
$$

Indeed at most one row of $P$ lies over any tuple of $v_j$ cells;
its weight is at most the product of those cell maxima, and summing
over all cell tuples proves the inequality. Every $P_j$ is
range-feasible. The representative selection in Theorem 4.4 turns
each bracket into the mass of a reply-basis test subset, bounded by
$\mathcal U_{I_j}(w_j)$. This proves one direction of (OCB.36).
The product of maximizing constituent test supports is itself a test
support, with product mass, proving the other direction. This proof
also covers zero weights; it imposes no product structure on the
competing $P$.

On an actual scaffold, the paired targets and replies above the cut
are constants, while those below it are exactly the constituent paired
ports, in both directions by their fixed public prefixes. Zero-weight
states can be removed because $\mathscr R$ is hereditary. Thus the
product identity gives the scaffold equality in (OCB.37). The stability
bound follows since $\mathcal U$ is a maximum of subset probability
masses and every such mass changes by at most total variation.

Induct on any finite derivation. Ordinary leaves give $C\ge\mathcal U$.
By (OCB.36) every grouped leaf gives the same inequality. By the
scaffold identity and the inductive premise, a scaffold step does too.
The stability inequality proves it for a stability step. Conversely,
when $C\ge\mathcal U$, enumerate all finitely many test supports
and their rational subset masses to obtain an ordinary exhaustive leaf.
All these checks terminate and have finite rational comparisons.
Theorem 4.3 and the credited native scaffold and stability facts prove
all-size soundness. This characterizes exactly the stated rule class,
not $V_{\rm rec}$ or its range extension. $\square$

**Theorem 5.3 (an actual owner-only obstruction, including full support).**
Reuse the [NCM, Proposition 6.1][NCM] and [SRP, §3][SRP] motif:

$$
\begin{aligned}
A&=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,
\quad J=\langle B,A\rangle,
\quad Q=\langle C,A\rangle,\\
(u_0,u_1,u_2,u_3,u_4)
&=(C,J,\langle C,C\rangle,\langle J,J\rangle,\langle A,Q\rangle),
\qquad P=\{u_0,\ldots,u_4\}\subset S_3.
\end{aligned}
\tag{OCB.39}
$$

For every nonnegative whole-block $w$ supported on $P$,

$$
\mathcal U_3(w)=\sum_{s=0}^4w(u_s),\qquad
\beta_3(w)=\sum_{s=0}^4w(u_s)-\min_{s<4}w(u_s).
\tag{OCB.40}
$$

The pressure equality is the credited SRP theorem. The new class boundary
is that every $V_{\rm own}$ cap at the uniform law $\mu_0$ on $P$
is at least one, although $\beta_3(\mu_0)=4/5$. For the strictly
positive probability on the entire actual $S_3$,

$$
\mu_+=\frac{99}{100}\mu_0+\frac1{100}\operatorname{Unif}(S_3),
\tag{OCB.41}
$$

one has

$$
\beta_3(\mu_+)\le\frac{81}{100},\qquad
V_{\rm own}\text{ acceptance implies }
C\ge\frac{6091}{6150}>\frac{99}{100}.
\tag{OCB.42}
$$

These conclusions include every product grouping, scaffold step and
stability step of Definition 5.1.

Proof. The owner reply triples $(r_L,r_R,r_{RL})$ on the five states
are respectively

$$
(\alpha,\alpha,\mathsf{absent}),\quad
(\beta,\alpha,\mathsf{absent}),\quad
(\mathsf{branch},\mathsf{branch},\alpha),\quad
(\mathsf{branch},\mathsf{branch},\beta),\quad
(\alpha,\mathsf{branch},\mathsf{branch}).
\tag{OCB.43}
$$

They are distinct, and all three paired targets $L,R,RL$ are
self-decodable on $P$. Every target range has size at most four.
Thus $P\in\mathscr R_3$ and $\mathcal U_3(w)\ge w(P)$; the
total weight gives equality. SRP Theorems 1.2 and 3.2 give the other
equality of (OCB.40) for every native length, retaining all competitors.

Here is the actual native local fragment exhibiting the loss. In both
blocks of the credited paired fiber
$B_* =\{(u_s,u_{\tau(s)}):0\le s\le4\}$, where $\tau$ interchanges
$1,4$, put owners at $L,R,RL$. Use root constant $(0,0)$ and these
attained reply-to-factor tables:

| Target | Seed queried | Attained reply-to-factor values |
| --- | --- | --- |
| $L$ | own $L$ | $\alpha\mapsto(2,1),\ \beta\mapsto(1,0),\ \mathsf{branch}\mapsto(0,0)$ |
| $R$ | own $R$ | $\alpha\mapsto(2,1),\ \mathsf{branch}\mapsto(0,0)$ |
| $RL$ | own $RL$ | $\mathsf{absent}\mapsto(3,0),\ \alpha\mapsto(2,1),\ \beta\mapsto(1,0),\ \mathsf{branch}\mapsto(0,0)$ |
| $LR$ | own $L$ | $\alpha\mapsto(4,1),\ \beta\mapsto(3,1),\ \mathsf{branch}\mapsto(2,1)$ |
| $RR$ | own $R$ | $\alpha\mapsto(4,1),\ \mathsf{branch}\mapsto(2,1)$ |
| $LL$ | other block's $RL$ | $\mathsf{absent}\mapsto(3,0),\ \alpha\mapsto(2,1),\ \beta\mapsto(1,0),\ \mathsf{branch}\mapsto(2,0)$ |

Owner domains are exactly their replies in (OCB.43); unused entries
have the RRN guards or arbitrary allowed extensions. These are the
NCM native witnesses, now grouped by their actual owners. For each
of the five owned triples there exists an incoming $RL$ reply giving
local weight $w(u_s)$. Since the owner replies distinguish them,
$L_\eta(w)=w(P)$. Hence no probability on that entire joint owner
tuple can dominate the local potential with a smaller constant.
The two blocks must nevertheless use the same actual incoming owner
values, rather than their independently selected local maximizers.
With uniform motif weights the positive two-block rows of these tables
are exactly $B_*$ and have mass $5/25=1/5$; the local owner envelope
is one in each block. The full potential and compatibility zeros are
retained in this calculation.

At $D=4$, merge the five canonical trees
$\langle u_s,u_{\tau(s)}\rangle\in S_4$, naming all other canonical
states separately. Theorem 3.4 gives a full-family code with exactly
$15131-5+1=15127$ attained names, $15$ preparation Reads, maximum
length four, and $49$ submitted letters. A request $RbLL$ uses the
actual other-block word $R\bar bRL$, with $\bar L=R,\bar R=L$;
other targets use the table above or a constant. This is a canonical
full-family realization, distinct from NCM Proposition 6.2's larger
source-distinguishing code, and is deliberately nonoptimal.

Now $|S_3|=123$ and probability stability from NPC Theorem 6.1 gives
$\beta_3(\mu_+)\le4/5+1/100$. But
$\mathcal U_3(\mu_+)\ge\mu_+(P)=99/100+5/12300=6091/6150$.
Theorem 5.2 propagates this floor through every stated rule. Each full
alphabet coordinate has mass at least $1/12300$, proving the claimed
positive-support boundary.

The existing support-complete JTC joint leaf already certifies the
unperturbed cap $4/5$. Indeed among all thirty-one nonempty subsets
of $P$, a set omitting a core state has no hard target and mass at
most $4/5$. On the four core states the hard $LL$ vector has four
singleton cells, with squared norm $4/25$. On all of $P$ it has
cells $\{0,4\},\{1\},\{2\},\{3\}$, with squared norm $7/25$.
Both are at most $16/25$. The other six targets have their NCM
own-coordinate witnesses. Hence every support in the joint test
passes, and stability also gives the full-support cap $81/100$.
The obstruction is to owner-only incoming maximization and its specified
closure rules; it does not obstruct full joint methods. In particular it
does not refute optimizer-cofinality after changing $\mu$, general
multi-owner joint relations, lawful recuts or global recoloring.
$\square$

## 6. Actual code fibers and the imported-entropy boundary

**Definition 6.1 (conditional ownership on an original source slice).**
Fix $d\ge1$, $H\ge0$, $n=2^H$ and $D=d+H$. Place canonical
blocks $X_i$ at the fixed actual frontier of $T_H$ in the right
subtree of one source. Give them any analytical product law
$\prod_i\mu_i$, and restrict an arbitrary original correct complete
code $E$ to this slice. No law or seed vector is given to its reader.
For each nonempty name fiber $B_e$, choose any complete native witnesses
containing it and apply RRN normalization. Let $O_i$ be the tuple of all
actual seed-owner replies in block $i$, in a fixed public order for
that name. Owner choices can depend on $e$ and the tuple can be empty.
Tuples of different lengths can be regarded as elements of a finite
disjoint union; all statements below are conditional on $E$.

For each name, $O_i$ is a function of $(X_i,E)$, and $(E,O_1,\ldots,O_n)$
determines $X$ on the actual fiber. This holds even when the complete
witness solution set strictly contains the fiber. Define

$$
B_{\rm local}=\sum_i I(X_i;E),\qquad
B_{\rm import}=\sum_iH(X_i\mid O_i,E),\qquad
\operatorname{TC}(O\mid E)=\sum_iH(O_i\mid E)-H(O\mid E).
\tag{OCB.44}
$$

**Theorem 6.2 (the representation-invariant budget and an extensive
native failure of owner-correlation-only accounting).** For every
code, law and witness choice in Definition 6.1,

$$
\begin{aligned}
H(E)&=B_{\rm local}+B_{\rm import}+\operatorname{TC}(O\mid E)
       \le\log_2|E[\mathcal F_D]|,\\
B_{\rm import}+\operatorname{TC}(O\mid E)
 &=\operatorname{TC}(X\mid E)
  =H(E)-\sum_iI(X_i;E).
\end{aligned}
\tag{OCB.45}
$$

The combined term is independent of the witness completion. Neither
summand separately is invariant. There exist actual full-family codes
for every dyadic $n\ge2$ with the same actual fibers admitting two
legal witness choices with respective values

$$
(B_{\rm local},B_{\rm import},\operatorname{TC}(O\mid E))
=(0,n/2,0)\quad\text{and}\quad(0,0,n/2).
\tag{OCB.46}
$$

Consequently a proposed bound
$\operatorname{TC}(X\mid E)\le\operatorname{TC}(O\mid E)+a_n$
with $a_n=o(n)$ fails even when the owned groups are conditionally
independent in actual native data.

Proof. For each actual fiber, owner-reply reconstruction is injective
and the owner tuple is a deterministic function of the blocks. Hence
$H(X\mid E)=H(O\mid E)$. Also

$$
H(X_i\mid E)=H(O_i\mid E)+H(X_i\mid O_i,E).
$$

Subtracting gives
$\operatorname{TC}(X\mid E)=B_{\rm import}+\operatorname{TC}(O\mid E)$.
The blocks are independent before conditioning, and $E$ is a
deterministic function of them on this fixed source slice. Therefore

$$
\operatorname{TC}(X\mid E)
=\sum_iH(X_i\mid E)-H(X\mid E)
=H(E)-\sum_iI(X_i;E).
$$

All three terms are nonnegative and the full attained alphabet bounds
$H(E)$. These are the credited finite chain rules and RRN's injectivity
applied on the actual fibers, without changing their conditional law.
The native content is the invariant accounting and the following
quantified realization, not a new standalone chain rule.

Write $\operatorname{bit}(0)=\alpha$, $\operatorname{bit}(1)=\beta$,
$u_{ab}=\langle\operatorname{bit}(a),\operatorname{bit}(b)\rangle$
and $U=\{u_{ab}:a,b\in\{0,1\}\}\subset S_2$. Let $n=2^H$,
$H\ge1$, $r=n/2$ and $D=H+2$. Group consecutive actual blocks as

$$
X_{2j-1}=u_{a_jb_j},\qquad X_{2j}=u_{c_jd_j},\qquad
E=(b_j\mathbin\oplus c_j)_{j=1}^r.
\tag{OCB.47}
$$

Under independent uniform blocks in $U^n$, this has $2^r$
equiprobable names and $2^{3r}$ rows per actual fiber, each of mass
$2^{-r}$. Each one-block projection is $U$, and each block is
independent of the exported parity vector, so $B_{\rm local}=0$.

For the first witnesses, in each pair keep the three seeds $a_j,b_j,d_j$
owned at odd $L$, odd $R$ and even $R$. Internal block roots are
constant branch. Even $L$ reads the odd $R$ port and decodes the
bit xor the known name bit $e_j$. Other leaf targets read their own
owner. Guard all leaf seeds to alpha or beta and use factors $(2,1)$
and $(1,0)$ for these actual replies. These are complete native
representative equations whose full solution set is exactly the
specified $B_e$: they impose precisely $c_j=b_j\oplus e_j$.
Conditional on $E$, all $3r$ retained owner bits are independent
uniform bits. Odd blocks are determined by their own owner tuples;
each even block still has one independent imported bit given its
own $d_j$ and $E$. Thus $\operatorname{TC}(O\mid E)=0$ and
$B_{\rm import}=r$.

For the second witnesses use self Reads at every leaf. Their complete
solution set is $U^n$, which contains the same actual $B_e$ but is
not asserted to equal it. On the unchanged conditional law of the
actual fiber, each $O_i$ now determines $X_i$. Thus $B_{\rm import}=0$
and $\operatorname{TC}(O\mid E)=\operatorname{TC}(X\mid E)=r$.
Replacing the fiber by its completion would erase exactly this term
and is not part of the argument.

The local mass accounting agrees with both choices. Under uniform
$\mu(U)=1$, in the first representation odd blocks have $L_i=1$
and even blocks $L_i=1/2$; the remaining defects of (OCB.31) vanish,
giving mass $2^{-r}$. In the self-Read completion $L_i=1$ for all
blocks, but restricting to the actual $B_e$ gives owner correlation
$r$ and all other defects zero. Its mass is still $2^{-r}$.
Here (OCB.31) is applied to that retained subrelation; the mass of
the full self-Read completion itself is one.

To realize the complete code on every original variable shape, scan
all $Rq$, $q\in W_D$, before the request. If $\pi_D(v)$ lies in
$T_H(U^n)$, export its parity vector; otherwise export its own distinct
canonical name. The complete attained alphabet is exactly

$$
|S_D|-4^n+2^r.
\tag{OCB.48}
$$

Every name is attained. Scan bounds are (OCB.23). At $H=1$, these
are $109$ names, seven Reads and seventeen submitted letters.
At a parity name, above-cut and block-root targets are branch;
leaf targets use one installed self or cross-owner original-root
literal, of length at most $H+2=D$. The name supplies the parity
decoder, not an extra observation. Canonicalization preserves the
queried replies and requested factors throughout its full variable-shape
inverse image. Singleton canonical names need zero Reads. The credited
all-count decoder supplies every subsequent authentic count, and all
other acquired dependence is isolated as in Theorem 3.4. Table, work,
workspace, predictor, count and physical service costs remain separate.

Finally $r=n/2$ along every dyadic $n$, so any $a_n=o(n)$ eventually
fails the proposed shortcut. This family has a locally admissible
support $U$ and $\beta_2(\operatorname{Unif}(U))=1$. It is a precise
obstruction to the stated accounting rule, not an optimized pressure
obstruction or a new rate lower. $\square$

## 7. A retained-entropy consequence for the original observer

**Definition 7.1 (credited type profile).** For a symbol-count vector
$\nu$ of length $n$, let $T_\nu\subseteq S_d^n$ be its type class
and let

$$
a_n(\nu)=\max_{B\text{ admissible}}|B\cap T_\nu|.
$$

Use the continuous concave function $\alpha_d$ of [NPC, Theorem
4.3][NPC], characterized for rational $p$ and $rp$ integral by

$$
\alpha_d(p)=\sup_{k\ge1}(kr)^{-1}\log_2a_{kr}(krp),\qquad
0\le\alpha_d(p)\le H(p).
\tag{OCB.49}
$$

NPC supplies $\sigma_d=\max_p[H(p)-\alpha_d(p)]$. This profile and
its convergence are credited; no effective length modulus is assumed.

**Theorem 7.2 (same-source conditional capacity and compulsory entropy).**
For any admissible $B\subseteq S_d^n$ and any law $P$ on $B$, let
$p=n^{-1}\sum_i\mathcal L_P(X_i)$ be its mean one-block marginal.
Then

$$
H(P)\le n\alpha_d(p).
\tag{OCB.50}
$$

For any deterministic complete admissible-fiber code $c$ on $S_d^n$
and any joint law $X$ with mean marginal $p$,

$$
H(c(X))\ge H(X)-n\alpha_d(p).
\tag{OCB.51}
$$

In particular every original complete code restricted to the actual
perfect source slice with $n=2^{D-d}$ iid $\mu$ blocks satisfies

$$
\log_2|E[\mathcal F_D]|\ge H(E)
\ge n\bigl(H(\mu)-\alpha_d(\mu)\bigr).
\tag{OCB.52}
$$

Proof. Approximate $P$ by laws $P_m$ on the finite row alphabet $B$
with denominator $m$, converging to $P$. The arrangements of $m$ rows
with that row type concatenate injectively into $B^m$, which is
admissible by the native product rule. All concatenations have the
same $S_d$-symbol type with empirical law $p_m\to p$. The elementary
multinomial type bound, also used in NPC, gives at least

$$
(m+1)^{-|B|}\,2^{mH(P_m)}
$$

distinct concatenations. Repetition of any finite type set in (OCB.49)
therefore gives

$$
\alpha_d(p_m)\ge \frac{H(P_m)}n
                    -\frac{|B|\log_2(m+1)}{mn}.
$$

Entropy and $\alpha_d$ are continuous on their finite simplexes.
Taking $m\to\infty$ proves (OCB.50), including zeros in $P$.
Conditional on each attained code, apply (OCB.50) to its actual fiber
and actual conditional law. Concavity gives
$H(X\mid c)\le n\sum_e\Pr(e)\alpha_d(p_e)\le n\alpha_d(p)$.
Determinism yields (OCB.51).

For the original-task assertion restrict the same code to the fixed
actual scaffold, without recoloring any fiber. The argument in
[NPC, Theorem 7.1][NPC] shows that each fiber is admissible: every
original-root query is constant outside the blocks or enters exactly
one actual block; any finite suffix reduces to one boundary reply
in that same donor block or a constant. Equal selected replies give
identical predictors and hence equal factors by correctness for every
subsequent count. No donor is required to be the target block and no
correlated fiber is replaced by a product. Under iid blocks,
$H(X)=nH(\mu)$, proving (OCB.52).
This is an entropy lower against every original competitor. It neither
changes the complete attained-alphabet objective nor gives an attaining
alphabet-minimal encoder. $\square$

**Theorem 7.3 (a strict source-specific gain on the credited core).**
Use the four core states $u_0,u_1,u_2,u_3$ from (OCB.39). Give them
probabilities $\mu=(4,3,2,1)/10$, with zero probability elsewhere in
$S_3$. Then

$$
\alpha_3(\mu)=H(4/10,3/10,3/10),\qquad
H(\mu)-\alpha_3(\mu)
=\frac15\log_2\frac32+\frac1{10}\log_2 3.
\tag{OCB.53}
$$

For every $D\ge3$ and every original complete code, under the
analytical law of $n=2^{D-3}$ such actual iid blocks,

$$
H(E)\ge n\left(\frac15\log_2\frac32+\frac1{10}\log_2 3\right)
       >n\log_2\frac{10}{9}.
\tag{OCB.54}
$$

The latter is the maximum-fiber-mass entropy bound for this same law;
the strict improvement concerns that source-specific consequence.

Proof. On the four-state core, credited SRP pressure is the sum of
the three largest weights. For $w=(4,3,3,3)/10$ on this core and
zero elsewhere, it is one. Every word in a type-$\mu$ class has
$w$-weight $\prod_sw_s^{n\mu_s}$, so the all-size mass bound gives

$$
\alpha_3(\mu)\le-\sum_s\mu_s\log_2w_s
                    =H(4/10,3/10,3/10).
$$

This use of zero weights requires no boundary differentiation or
unproved variational extension. For the reverse inequality write

$$
\mu=\frac23(4/10,3/10,3/10,0)
        +\frac13(4/10,3/10,0,3/10).
$$

Each constituent triple is identified by one native literal on the
credited core, hence its entire Cartesian powers are admissible and
its type capacity equals its entropy. The two entropies coincide.
Concavity of $\alpha_3$ supplies the matching lower. Subtracting
entropies gives (OCB.53), and Theorem 7.2 gives (OCB.54).

For this same $\mu$, SRP gives $\beta_3(\mu)=9/10$.
A bound of $(9/10)^n$ on each actual name probability implies only
$H(E)\ge n\log_2(10/9)$ by the maximum-atom argument.
The strict inequality in (OCB.54) follows exactly from
$27/4>(10/9)^{10}$ after raising to the tenth power. The source laws
in the two comparisons are identical. No source-dependent request,
new observation, physical randomness service or preparation prior is
introduced. The conclusion is a native application of the credited
core pressure and profile to complete original names, not a new
core-pressure theorem or a numerical improvement of $\lambda$.
$\square$

**Theorem 7.4 (one-composition entropy ceilings give all-length caps).**
Fix $d$, a probability $\mu$ on $S_d$, its nonempty support $F$, and
$m=\min_{x\in F}\mu(x)>0$. Suppose two real numbers $L,U$ satisfy

$$
\alpha_d(\mu)\le H(\mu)-L,\qquad \sigma_d\le U.
\tag{OCB.59}
$$

Then for every $0<\tau\le m$,

$$
\beta_d(\mu)\le
2^{-L+(U-L)/\tau+2\tau/m}.
\tag{OCB.60}
$$

Thus any rational cap $C$ at least this expression bounds every length
and complete original native template and has the original consequence
(OCB.11). A finite native cover gives an upper $U$ through
$\sigma_d\le N^{-1}\log_2K_d(N)$. The other premise is an all-length
entropy ceiling at the one specified composition; it is not supplied
by a finite type computation. For rational $\mu$ of denominator $r$,
that premise is exactly

$$
\forall k\ge1\quad a_{kr}(kr\mu)
              \le2^{kr(H(\mu)-L)}.
\tag{OCB.61}
$$

There is no assumption on the number of blocks, their donor topology,
their shared seed incidences or their once-owned joint weights.

Proof. The pressure variational identity of NPC Theorem 5.2 has the
following face version for this $\mu$:

$$
\log_2\beta_d(\mu)
=\max_{p\in\Delta(F)}
 \left[\alpha_d(p)+\sum_{x\in F}p(x)\log_2\mu(x)\right].
\tag{OCB.62}
$$

Here it is used only as an intermediate identity, with its boundary
conditions justified as follows. Positive-mass rows lie in $F^n$;
their type intersections remain admissible, and each type maximum is
bounded by $2^{n\alpha_d(p)}$ by (OCB.49). At most $(n+1)^{|S_d|}$
types occur. The product closure of actual native relations gives
supermultiplicativity of maximal masses, whose logarithms have a
finite lower remainder bound because $F$ is nonempty. Their normalized
limit equals the all-length supremum. Letting $n\to\infty$ removes
the polynomial type count and proves the upper direction of (OCB.62).
Attaining type sets along multiples of every rational $p\in\Delta(F)$
give its lower direction by (OCB.49); continuity on that face supplies
all $p$. No logarithm of a zero coordinate is taken.

For any $p\in\Delta(F)$ put $q=(1+\tau)\mu-\tau p$ on $F$.
It is normalized and nonnegative, since $\tau\le m$. Concavity at
$\mu=(\tau p+q)/(1+\tau)$ and the first premise of (OCB.59), together
with $\alpha_d(q)\ge H(q)-U$, imply

$$
\alpha_d(p)+\sum_xp(x)\log_2\mu(x)
\le -L+\frac{U-L+D_2(q\|\mu)}{\tau}.
\tag{OCB.63}
$$

Indeed
$D_2(q\|\mu)=(1+\tau)H(\mu)-H(q)
                  +\tau\sum_xp(x)\log_2\mu(x)$,
which gives precisely (OCB.63) after substitution. This uses the same
whole-block distributions on the same alphabet throughout.

The elementary inequality $\ln t\le t-1$ gives

$$
D_2(q\|\mu)\le\frac{\chi^2(q,\mu)}{\ln2},\qquad
\chi^2(q,\mu)=\tau^2\left(\sum_x\frac{p(x)^2}{\mu(x)}-1\right)
       \le\frac{\tau^2}{m}.
$$

Since $\ln2\ge1/2$, (OCB.63) is at most
$-L+(U-L)/\tau+2\tau/m$. Maximize using (OCB.62), proving (OCB.60).
For rational $\mu$, (OCB.49) makes its ceiling equivalent to all of
(OCB.61), in both directions. This is why one finite checked type is
insufficient. Finally (OCB.11) applies to the resulting genuine
all-length cap and all original competitors. Rational enclosures of a
proved endpoint are numerical precision choices, separate from proving
(OCB.61). This implication constructs neither a cofinal family of those
ceilings nor an effective length modulus. $\square$

## 8. Universal scope and the unclosed effective obligation

**Definition 8.1 (the remaining universal certificate problem).** At
each $d\ge1$, the missing premise remains a total computable
predicate $V(d,\mu,C,\pi)$ on rational probabilities, positive
rational caps and finite strings, satisfying both

$$
V(d,\mu,C,\pi)\Longrightarrow
 \forall n\ge1\ \forall\Theta\quad
 \sum_{x\in C_\Theta}\prod_i\mu(x_i)\le C^n
\tag{OCB.55}
$$

and, for every positive rational $\epsilon$, existence of an accepted
pair with $-\log_2C>\sigma_d-\epsilon$. The equivalent temporal
carrier of Theorem 2.3 retains every actual owner, guard, seed incidence,
compatibility zero and arbitrary full joint block weight. Multi-owner
joint relations of unbounded size are explicitly permitted; the
owner-only language of Definition 5.1 is a restricted sufficient
method, not a replacement definition of admissibility or success.

An alternative sufficient bridge is an effective bound

$$
\sigma_d\ge n^{-1}\log_2K_d(n)-\eta_d(n),\qquad
\eta_d(n)\longrightarrow0,
\tag{OCB.56}
$$

uniform over the original complete arbitrary-donor competitors at the
specified depth. Neither (OCB.55)'s cofinality nor (OCB.56) is asserted
here. In the entropy route, a finitely checkable cofinal family of
ceilings (OCB.61) is likewise unconstructed; Theorem 7.4 is the
quantified conditional transfer, not such a family. Theorem 2.3 proves an exact carrier, Theorem 3.2 rejects a specified
exact elimination class, and Theorem 5.2 characterizes a specified
sound cap class. Their quantifiers give no stronger impossibility
conclusion. A failure at a fixed $\mu$ does not disprove cofinality
whose optimization varies $\mu$.

**Assumption 8.2 (credited endpoints and distinct supplier domains).**
[NCE, Theorems 6.1–6.2][NCE] and [D3, Theorems 2.3 and 4.1][D3]
retain

$$
\frac18\log_2\frac{33}{13}\le\lambda<\frac3{16},
\qquad M_1(3)=4.
\tag{OCB.57}
$$

General exact $M_1(D)$, sharp $\lambda$, effective all-size optimizer
coverage and broader source/space/time mutual recovery are unclosed.
[RCE][RCE] supplies the distinct old-joint-calculus acceptance boundary
and range extension; [JPL][JPL] supplies the core-atlas ceiling and
separable-majorant obstruction. None is reasserted as a new result of
this source. The owner-only obstruction here retains the actual motif
joint relation and does not exclude either existing full joint rules
or arbitrary cross-owner boundary laws. [GCB][GCB]'s graph-cover and
Bethe statements have their specified incidence hypotheses; no generic
graphical upper bound is substituted for (OCB.55).

The native operational recovery used throughout is exactly

$$
(E(t),D,p,\text{at most one actual reply})
\longrightarrow\Gamma_p(t)
\longleftrightarrow\bigl(r_{\rho^kt}(p)\bigr)_{k\ge0}.
\tag{OCB.58}
$$

The inverse recovers first branch count and alpha-stage presence. It
does not recover a whole source, an unknown age, unseen history,
authentication or physical spacetime. Analytical owners, selectors,
conditional laws and entropy defects supply no additional reader inputs.

**Assumption 8.3 (mathematical sources and transfer conditions).**
Rectangular support and primitive-positive closure have the standard
meanings of [Dyer–Richerby, §§3–4][DR]. The disjoint-fiber description
of a single rectangular relation is a mature ingredient of Theorem
2.2. Strong rectangularity requires the corresponding property after
all primitive-positive definitions; Theorem 3.2 gives the exact native
failure of that extra premise. No counting dichotomy is transferred
to regularized native pressure.

The entropy and relative-entropy identities in Theorems 4.3 and 6.2
are mature finite common-law tools; [Madiman–Tetali, Proposition II][MT]
uses actual fractional covers or packings of a specified family of
subsets of one law. Arbitrary native incidences supply no fixed
fractional-cover premise or optimizer coverage. Theorem 7.2 instead
uses the credited native product/type profile on the actual fibers.
The finite LP duality in Theorem 4.4 and sum-product elimination in
Theorem 3.2 are also ingredients, not standalone novelty claims.

[Gaubert–Stott, Theorem 7][GS] assumes a finite family of fixed-size
nonnegative matrices and positive irreducibility to obtain its explicit
approximation factor. No representation of every overlapping native
joint potential by such fixed-dimension matrix products, with both
pressure inequalities and the paid same-source correspondence, is
assumed here. Finite alphabets, binary primitive relations and exact
finite sums alone supply neither that representation nor (OCB.56).

The source declaration [FiniteNaturalJoin, `join_covers`][D5J] requires
both input relations to cover the same full assignment. It proves no
automatic global realization or all-size estimate. The actual realization
and unique lifts used here are proved in Theorems 2.2, 3.2 and 3.3.
[NativeFiniteRootMinimax, `finite_root_minimax`][D5M] concerns an
attained three-reply chart and complete predecessor-row recovery.
[NativeEffectiveRootCriterion, `effective_native_birth_provenance` and
`returned_native_reader`][D5E] requires a prefix-free cut, a complete
row with nonempty `OriginFiber`, $r\ge1$, a returned package and
compatible acquired image values; its source is the substituted one.
Those target and handoff conditions differ from (OCB.1)–(OCB.2).
Neither declaration is used as an all-length cap verifier.

[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DONOR_NETWORKS_AND_REPAIR_COST.md
[NCM]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CORRELATED_MEMORY_LOWER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CYCLIC_ENTROPY_LOWER.md
[D3]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[NPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRODUCT_PRESSURE_COMPLETENESS.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[RRN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[RCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[JPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_POTENTIAL_LIMITS.md
[JTC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_TARGET_CERTIFICATES.md
[SRP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SINGLE_RESIDUAL_PRESSURE.md
[GCB]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GRAPH_COVER_BETHE_BOUNDARIES.md
[D5N]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[D5J]: ../../../D5/S0/Certificates/FiniteNaturalJoin.lean
[D5M]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean
[D5E]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveRootCriterion.lean
[DR]: https://arxiv.org/html/1003.3879v4 "Martin Dyer and David Richerby, An Effective Dichotomy for the Counting Constraint Satisfaction Problem, §§3–4"
[MT]: https://arxiv.org/html/0901.0044v2 "Mokshay Madiman and Prasad Tetali, Information Inequalities for Joint Distributions, with Interpretations and Applications, Proposition II"
[GS]: https://arxiv.org/html/1805.03284v1 "Stéphane Gaubert and Nikolas Stott, A convergent hierarchy of non-linear eigenproblems to compute the joint spectral radius of nonnegative matrices, Theorem 7"

## 追加锚（本行以下为增补区）
