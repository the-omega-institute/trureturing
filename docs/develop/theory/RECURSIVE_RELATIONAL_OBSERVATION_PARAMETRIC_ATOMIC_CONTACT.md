# Parametric atomic contact for complete signed native rows

## 1. Entire sources and the joint question

**Definition 1.1 (finite native sources).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle s,t\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_j&=\rho^j\alpha\qquad(j\in\mathbb N).
\end{aligned}
\tag{PAC.1}
$$

All sources are nonempty finite ordered free binary trees. There is no
common size or rank bound. The operation $\rho$ has the interpreted laws
(PAC.1); it is not an additional free constructor. An original address is
a finite word over $\{L,R\}$, including the root $\varepsilon$. Its reply
is $\alpha$, $\beta$, $\mathsf{branch}$ or $\mathsf{absent}$. Put

$$
u\equiv_hv\quad\Longleftrightarrow\quad
\forall |p|\le h\quad r_u(p)=r_v(p).
\tag{PAC.2}
$$

Depth is inclusive, and strict descendants of a leaf are absent.

**Definition 1.2 (complete retained input).** Fix
$I=(P,R,H_0,H_{\rm rel},Q,N)$ as in [ARH, Definitions 1.1–1.2][ARH].
Both cuts are finite and prefix-free. A complete row at a cut retains its
ordered reached subset, its entire concrete exterior with numbered holes,
and the equality partition of the whole native subtrees at those holes.
In particular the empty cut retains the whole source, and the root cut has
one hole. The attained old row $R$ includes all three fields.

A literal $(a,p,c)$ means $r_{\rho^a u}(p)=c$. A signed record
$(a,p,b,q,\bowtie)$ means

$$
p\in\operatorname{Pos}(\rho^a u)\ \land\
q\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\qquad \bowtie\in\{=,\ne\}.
\tag{PAC.3}
$$

Absence invalidates either sign. Lists retain repetitions, and every
record inside a realization concerns the same original source. Define

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\},
\qquad
D_r=\{u\in D:R_Q(u)=r\}.
\tag{PAC.4}
$$

Thus the entire old exterior, old absent addresses, repeated old classes,
all old cross-class and off-task inequalities, every literal, every sign,
and both endpoint guards are imposed jointly. Rows outside any selected
family remain part of $D$.

**Definition 1.3 (selected joint contact).** Let $B$ be any supplied finite
set of distinct attained complete original $Q$-rows, $|B|\ge2$. Set

$$
J_B(h)\quad\Longleftrightarrow\quad
\exists (u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\quad u_r\equiv_hu_s.
\tag{PAC.5}
$$

The witnesses are alternative finite originals for one common retained
input, not a single source assigned incompatible labels. All rows in $B$
share one prefix; separately chosen pairwise witnesses do not suffice.

**Assumption 1.4 (paid actual service).** Service conclusions use exactly
[ARH, Assumption 1.3 and Proposition 2.1][ARH]. A public paid source-total
producer acquires the old row, literals and whole-subtree comparisons on
one original-root register and reaches authentic common epoch $N$, at
least every recorded epoch. Conditional on the complete accessible-state
cut, its retained state has exactly fibre $D$. Every accessible
source-bearing cache, address, count, length, control, timing field,
permission, archive and handle belongs to that premise.

The service starts at the actual $\rho^N u$. Its source operations are paid
four-valued original-root reads, forward same-register applications of
$\rho$, and absorbing halt. Local computation observes only common data
and acquired replies. There is no chart, rank, equality, selector,
old-version, source-identity, reset, reroot, clone or limit-tree port.
Acquisition, new reads, literal lengths, updates, local work, memory,
preparation, installation and retention are separate resources.

## 2. Exact atomic anchor and arbitrary signed companions

**Assumption 2.1 (entire atomic-output anchor).** For some $r_\ast\in B$
supply an exact finite cover

$$
D_{r_\ast}=\bigcup_{b\in\mathcal A}
 \{U_b(\mathbf n):\mathbf n\in\mathbb N^{k_b},\ S_b(\mathbf n)\},
\qquad
U::=g\mid T_{n_i+a}\mid\langle U,U\rangle.
\tag{PAC.6}
$$

Here $g\in\mathcal T$ and $a\ge0$ are fixed finite data, and $S_b$ is
an effective Presburger formula. Repeated coordinates are shared, and
$S_b$ may correlate all ranks. There is no residual tree in the source
output $U_b$. Invisible coordinates may have been projected away only by
an exact support projection. Both source directions are required: every
admitted image is in the whole $D_{r_\ast}$, and every source of that
stratum is reconstructed as itself by one piece. Coordinates need not be
unique. Neither a finite source image nor a finite accumulation set is
assumed. Recognition of an undiscovered anchor is not a premise supplied
by calling a stratum atomic.

**Definition 2.2 (companion covers).** For each $r\ne r_\ast$ use the exact
finite signed cover

$$
\begin{aligned}
D_r&=\bigcup_{b\in\mathcal C_r}
 \{\Theta_{r,b}(\mathbf v,\mathbf z):
     P_{r,b}(\mathbf v)\land\Delta_{r,b}(\mathbf v,\mathbf z)\},\\
\Delta_{r,b}&=\bigwedge_\ell A_{r,b,\ell}\ne A'_{r,b,\ell},\\
A&::=g\mid T_{v_i+a}\mid\rho^e z_j\mid\langle A,A\rangle.
\end{aligned}
\tag{PAC.7}
$$

All exponents and offsets are fixed nonnegative integers; $P_{r,b}$ is
Presburger. Before the displayed native negatives, the carrier is the
full Cartesian product $\mathbb N^{k_{r,b}}\times\mathcal T^{m_{r,b}}$.
There is no residual image, normality, navigation or positive-equation
filter left outside $P$ and $\Delta$. Repeated names share their entire
values. The source maps may overlap and may be nonfunctional in the ranks;
there is no common-skeleton or independent-rank premise.

Here is the actual source reduction for (PAC.7), consuming [NIC,
Theorems 3.2–3.3, Proposition 3.5 and Theorem 4.3][NIC]. Choose an original
pattern depth beyond every old and target cut address and every record
endpoint length. A finite source has its actual pattern, every early leaf,
and its actual reached-frontier subtrees. Fixed $\rho$ powers preserve
original branch nodes and expand early leaves into fixed finite trees.
Navigation to a listed endpoint therefore yields an exact native expression
or an absent endpoint in each finite case. Either sign is rejected in the
absent case. A reached case retains the entire native comparison at its
actual epochs. Each repetition uses the same frontier names.

For each old or target label, retain the reached set and equality of its
whole mask with the supplied concrete mask; every uncut frontier stays in
that expression. Together these give exactly the concrete exterior.
Retain every pair of reached holes as an equality or a disequality according
to the complete partition, including old classes outside $Q$. Thus each
case has a whole source term $W(\mathbf x)$ and a finite Boolean native
formula in its entire declared tuple, with both original-source directions.
The actual source chooses its actual case and is recovered by filling $W$.

Apply NIC 3.2 to all positive equations in a signed disjunct. Its connected
block-offset graphs give one minimum-potential native residual per sort;
all other blocks are its nonnegative fixed translates. Crucially, the
constructed positive image deliberately permits arbitrary finite native
residuals. NIC 3.1 proves sound expansion even when an assembled ambient
code is not normal: expanding a formerly ordinary primitive cherry still
satisfies the original native pairing equation. This removes canonical
branch identity only, introducing overlap, not a new native solution.
Conversely an actual original assignment chooses its genuine canonical
branch; its actual ranks and its normal minimum block reconstruct every
name as the same value. No marker replacement is made in that converse.

Pull back every original negative literally by NIC 3.3 and substitute the
whole-tuple image into $W$. The result is (PAC.7), with fixed powers
distributed through pairs and ground terms. NIC 3.5 expressly identifies
its pre-negative carrier as the full Cartesian product. Both inclusions
therefore retain the entire $D_r$, its exact complete row and every guard;
no residual restriction is silently discarded. This verifies the domain
needed by [URR, Theorem 3.1 and Corollary 3.2][URR] and [SLP, §1][SLP]
for these constructed pieces. An arbitrary differently supplied image
piece requires its own such correspondence and is not presumed Cartesian.

## 3. Uniform matching of completed atomic descriptions

**Definition 3.1 (completion and finite descriptions).** Let
$\widehat{\mathcal T}$ be the space of finite or infinite ordered binary
trees, with leaf labels $\alpha,\beta$ and the four-valued prefix topology.
It is the closed valid-tree subspace of the countable product of the four
reply symbols, hence compact. Finite trees are isolated by their finite
full prefixes. Pairing is continuous. Extending $\rho$ at leaves and
branches gives a continuous, prefix-nonexpanding operation. Indeed matching
leaf roots have equal finite images, and matching branch roots reduce to
the children at one smaller depth; induction on the requested depth proves
nonexpansion, including absence. Iterate for every fixed exponent.

Let $\Omega$ be the unique completion with a branch at every address.
[ABC, §1.3][ABC] supplies the atomic recurrence and injective indices;
[NLC, Lemma 3.1][NLC] gives $\mu(T_j)=\lfloor j/2\rfloor$. Thus
$T_j\to\Omega$ as $j\to\infty$, and

$$
j\ge2h+2\quad\Longrightarrow\quad T_j\equiv_h\Omega.
\tag{PAC.8}
$$

A finite generalized description has grammar

$$
X::=[q]\mid[\infty]\mid F(X,X),
\qquad E([q])=T_q,\quad E([\infty])=\Omega,
\quad E(F(X,Y))=\langle E(X),E(Y)\rangle.
\tag{PAC.9}
$$

There is one $[\infty]$ symbol: all divergent atomic coordinates have the
same completion $\Omega$, even though their actual finite ranks remain
separate in the support. This symbol is not a variable or a finite source.
The finite ranks $q$ are natural parameters or guarded affine expressions.

**Lemma 3.2 (uniform symbolic matching and exact preimages).** Fix one
anchor piece, one companion piece for every other selected row, and a
finite/divergent mode on their combined rank tuple. Names in different
source copies are renamed apart; every shared occurrence within a copy is
retained. Let $F$ be the finite
coordinates, $A$ the divergent coordinates, and let $\mathbf c$ denote the
values at $F$. Replace their atoms respectively by $T_{c_i+a}$ and
$\Omega$. The anchor becomes $K(\mathbf c)$, a finite description of the
form (PAC.9).

There is a terminating finite compiler, uniform over all $\mathbf c$, for
completed equality of all these source maps with $K(\mathbf c)$. It
returns finitely many cases $\tau$ with Presburger guards
$E_\tau(\mathbf c,\mathbf d)$ and a generalized description
$Z_{r,j,\tau}(\mathbf c,\mathbf d)$ for each source-visible residual.
The auxiliary natural indices $\mathbf d$ obey fixed affine equations.
In a case, completed equality holds exactly when its guard holds and every
visible residual equals its specified $Z$. Repeated occurrences impose
equality of their specified values. Invisible residuals are unrestricted.
Finite versus infinite $Z$ is decided by the fixed description shape.

The compiler has both completed-source directions, including arbitrary
completed residual assignments; no finite occurs-check or free-unary rule
is used.

Proof. Normalize (PAC.9) from the bottom up by the two rules

$$
F([q+1],[q])\mapsto[q+2],\qquad
F([\infty],[\infty])\mapsto[\infty].
\tag{PAC.10}
$$

All other pairs remain. Finite cases are the ordinary ABC normalization,
and the second rule is $\langle\Omega,\Omega\rangle=\Omega$.
This normal form is faithful. By induction, a normal pair cannot expand to
a finite atom: the children would have to be consecutive finite atoms,
forcing the first forbidden pattern. It cannot expand to $\Omega$:
both children would have to be $\Omega$, forcing the second forbidden
pattern. A remaining pair cancels by actual ordered pairing. Finite atomic
roots have their unique rank by ABC; $\Omega$ is infinite. These cases
prove injectivity of normal descriptions by induction on their finite
syntax. A normal description is infinite precisely when it contains
$[\infty]$. Every other leaf expands to an actual finite atomic tree.

With parameter ranks, each pair contributes finitely many guarded cases
$q_L=q_R+1$ or its negation, or the fixed infinity case. The resulting
normal shapes are finite, and equality reduces to equality of corresponding
finite ranks and identical leaf types. This is the finite arithmetic
normalization of [CAR, Lemma 4.1][CAR], extended by the single second rule
in (PAC.10). No unbounded $T_c$ is expanded.

For a fixed address, a normal pair follows the selected child. The token
$[q]$ branches exactly when $q\ge2$, with children $[q-1],[q-2]$;
$[\infty]$ has two $[\infty]$ children. The cases $q=0,1$ are leaves
and block a further edge. This navigation consumes the supplied finite
word, so its branch list is finite. Every reached subtree again has a
finite generalized description. Introduce a fresh natural index with an
affine defining equation whenever an index is subtracted. Nonnegativity is
a guard, and no truncated subtraction is used.

The extended $\rho$ is injective on the entire completion. Its output root
is never $\alpha$; output $\beta$ comes only from input $\alpha$.
An input leaf $\beta$ outputs $\langle\beta,\alpha\rangle$, which cannot
be the output of an input pair because the latter's right child is in the
image of $\rho$, and $\alpha$ is not. All other possible paired outputs
therefore have paired inputs and cancel into equal child outputs.
Induction on finite input-prefix depth recovers every reply of two inputs
with the same output. Hence their completed trees are equal. Infinite
branches persist under $\rho$, so a finite output has a finite input.
Also $\rho\Omega=\Omega$, and injectivity gives its unique preimage.

On a normal generalized description, $\rho^e$ adds $e$ to every finite
rank, fixes $[\infty]$, and preserves every retained $F$: finite rank
differences and the forbidden infinity pattern are unchanged. Its unique
preimage among all completed trees exists exactly when every finite rank
is at least $e$, and is then obtained by subtracting $e$ there. To verify
exhaustiveness, decode one step by the root cases just proved. A finite
atomic output has its finite atomic preimage by ABC; $\Omega$ has only
$\Omega$; a normal non-atomic, non-$\Omega$ pair cannot come from a leaf,
so decode its children. This finite recursion proves the criterion,
including a pure $[\infty]$ description with no finite-rank guards.
Repeating gives the stated fixed-$e$ inverse, with arithmetic guards.

Now traverse each companion's finite source syntax against $K$. At a
source pair require a branch in the corresponding $K$ subtree and recurse.
A ground or finite/divergent atomic token is checked by description
equality. At each occurrence $\rho^e z_j$, take the unique preimage of
the matched subtree. Equalities between the preimages at all occurrences
of one name retain its sharing; different names may happen to have equal
values without being identified as coordinates. The traversal consumes
finite source syntax, and normalization and inversion consume finite
description syntax. This yields the asserted finite guards and $Z$.

Conversely, a completed assignment giving equal outputs follows exactly
those guarded navigation cases, and completed injectivity forces each
specified inverse. Any assignment of those inverses satisfying the guards
reassembles all source pairs and tokens to $K$. Hidden names affect no
output. These prove both directions. $\square$

## 4. Exact signed support and cofinal parameter loci

**Definition 4.1 (one arithmetic case).** For a chart tuple, mode and
matching case $\tau$, let $\mathbf p=(\mathbf c,\mathbf d)$ be the finite
parameters. Let $\mathbf w$ be the actual finite values of *all* divergent
rank coordinates, including companion and output-invisible coordinates.
Set $\mathbf v_F=\mathbf c$ and $\mathbf v_A=\mathbf w$.

In each companion substitute precisely the finite descriptions
$Z_{r,j,\tau}(\mathbf p)$ into its entire $\Delta_{r,b}$, and leave all
infinite visible descriptions and hidden residuals as free finite native
variables. Every finite substituted description is a finite pair template
over finite parameter atoms. Distribute its fixed powers; fresh natural
indices and affine equations put it exactly in URR's grammar. Before its
negatives, the remaining carrier is still the full Cartesian product.
Thus [URR, Corollary 3.2][URR] computes an exact Presburger predicate
$\Psi_{r,b,\tau}(\mathbf p,\mathbf w)$ for existence of one remaining
finite tuple satisfying *all* these negatives together.

Conjoin the matching guard, the anchor support, every companion policy,
and every $\Psi$:

$$
\Phi_\tau(\mathbf p,\mathbf w)=
 E_\tau(\mathbf p)\land S_b(\mathbf v_\ast)
 \land\bigwedge_{r\ne r_\ast}
   \bigl(P_{r,b_r}(\mathbf v_r)\land
           \Psi_{r,b_r,\tau}(\mathbf p,\mathbf w)\bigr).
\tag{PAC.11}
$$

This is the full joint support at the original ranks and the forced finite
residuals. It is not a chosen representative support. URR's section proves
and computes the existential projection; it does not replace the entire
source domain or promise to preserve prescribed prefixes.

Define the good finite-parameter locus by

$$
G_\tau=\left\{\mathbf p:
\forall M\in\mathbb N\ \exists\mathbf w\in\mathbb N^A\quad
\Phi_\tau(\mathbf p,\mathbf w)\land
\bigwedge_{i\in A}w_i\ge M\right\}.
\tag{PAC.12}
$$

The finite parameters precede every $M$ and every requested prefix depth.
The lower bounds apply simultaneously to one tuple in the complete joint
support. Zero dimensions have their literal singleton-product meanings.

**Theorem 4.2 (effective whole locus and one cofinal ray).** For every
case $\tau$, $G_\tau$ is effectively semilinear. One can decide whether it
is empty. If nonempty, one can produce a single fixed $\mathbf p_0$ and
finite vectors $\mathbf w_0,\mathbf q$ such that

$$
\Phi_\tau(\mathbf p_0,\mathbf w_0+t\mathbf q)
\quad(t\in\mathbb N),
\qquad q_i>0\quad(i\in A).
\tag{PAC.13}
$$

If $A=\varnothing$, the positivity condition is vacuous and this means one
feasible empty tuple. The procedure treats all finite parameters at once;
it does not enumerate $\mathbf c$ or a finite list of contacts.

Proof. Apply [Ginsburg–Spanier, Theorem 1.3][GS] to the Presburger set
$S_\tau=\{(\mathbf p,\mathbf w):\Phi_\tau(\mathbf p,\mathbf w)\}$.
This supplies an effective finite union of linear sets

$$
L_\ell=\mathbf b_\ell+
 \sum_{j=1}^{s_\ell}\mathbb N\mathbf a_{\ell j}
 \ \subseteq\mathbb N^{\mathbf p}\times\mathbb N^A.
\tag{PAC.14}
$$

Call a component eligible if, for every $i\in A$, some period has zero
$\mathbf p$ part and positive $i$th $\mathbf w$ coordinate. The sum of all
its zero-$\mathbf p$ periods is $(0,\mathbf q)$ with every $q_i>0$.
Adding $t(0,\mathbf q)$ to any point of that component proves cofinality
with that same finite parameter. In particular its base gives (PAC.13).

Conversely fix $\mathbf p$. The coefficient of any period with a positive
$\mathbf p$ coordinate is bounded in the fibre at $\mathbf p$, since
all periods and coefficients are nonnegative. If a component is ineligible,
choose a coordinate $i$ that no zero-$\mathbf p$ period increases. That
coordinate is bounded throughout this fixed fibre, including the bounded
contributions of all other periods. A finite union of ineligible components
therefore bounds the minimum of the $\mathbf w$ coordinates and cannot
satisfy all simultaneous lower bounds. For a cofinal fibre some eligible
component must contain a point with that $\mathbf p$. Consequently

$$
G_\tau=\bigcup_{\ell\text{ eligible}}\operatorname{pr}_{\mathbf p}L_\ell.
\tag{PAC.15}
$$

Projection gives the exact effective semilinear locus. Eligibility is a
finite period-coordinate test. For $A=\varnothing$, every component is
eligible and (PAC.15) is ordinary nonemptiness of the projected support.
An empty support has no components. This proves the algorithm and its
termination, not just a quantified notation for it. $\square$

The proof's arithmetic direction is supplied only after Lemma 3.2 and
(PAC.11) have eliminated the native tree operations. Presburger
decidability alone would not eliminate an unknown native predicate.

## 5. Terminating joint-prefix exclusion or actual finite realization

**Theorem 5.1 (parametric atomic-contact alternative).** For every input
of Definitions 1.1–1.3 satisfying Assumption 2.1, with the exact companion
covers constructed in §2, an effective terminating procedure returns
exactly one of these alternatives:

1. a finite $H\ge0$ such that $\neg J_B(H)$;
2. finite data, including one chart tuple, one mode, one matching case and
   one fixed finite parameter $\mathbf p_0$, defining an effective function
   $h\mapsto(u_{r,h})_{r\in B}$ of actual finite original sources satisfying
   $u_{r,h}\in D_r$ and $u_{r,h}\equiv_hu_{s,h}$ for all $r,s\in B$.

In the second alternative $\mathbf p_0$ is chosen once before all depths.
Divergent ranks and finite residual fillings may vary with $h$. Uniform
contact holds exactly when at least one of the finitely many $G_\tau$
is nonempty. These loci can contain infinitely many distinct contacts.

Proof. First establish completeness of the finite classification. Suppose
$J_B(h)$ for all $h$. Choose an actual joint witness tuple at each depth,
and use the exact covers to lift every source to actual finite coordinates.
A single chart tuple occurs at unbounded depths. Extract a subsequence on
which each rank coordinate is either a fixed natural number $c_i$ or
tends to infinity. Such an extraction is obtained successively over the
finitely many coordinates: a value occurring infinitely often can be
fixed; otherwise choose increasing lower bounds. Finitely many steps give
one simultaneous extraction, rather than separate unboundedness claims.

In the compact finite product of completed residual spaces extract a
further convergent subsequence. The anchor outputs converge to the finite
symbolic $K(\mathbf c)$. All companion outputs converge to that same tree,
since their differences from the anchor are invisible through increasing
prefix depths. Continuity of fixed powers and pairing gives exactly the
completed output equality used by Lemma 3.2. That lemma chooses one case
$\tau$ and fixed auxiliary indices $\mathbf d$. Its visible finite residual
values are forced, not selected among competing completions.

Every forced finite residual is isolated in the prefix topology. Thus at
late indices every such actual residual is exactly
$Z_{r,j,\tau}(\mathbf p)$, simultaneously for all names. The original
finite witnesses retain every native negative, both guards, all literals
and complete rows. They therefore prove $\Phi_\tau(\mathbf p,\mathbf w)$
at arbitrarily large simultaneous $\mathbf w$. This puts
$\mathbf p\in G_\tau$. No original sign, partition or row label was
passed to a limit: only completed output equality and eventual exactness
of finite coordinates were used.

Now suppose $G_\tau\ne\varnothing$. Theorem 4.2 supplies one
$\mathbf p_0$, a base $\mathbf w_0$ and a common positive ray. For a
requested inclusive $h$, choose a finite $t$ with
$w_{0,i}+tq_i\ge2h+2$ for every $i\in A$. This is one finite calculation
on the produced integers. Set the entire rank tuple to these divergent
values and the finite values $\mathbf c$. Equation (PAC.13) keeps all
rank correlations, including those imposed by every companion and every
signed-support projection.

Keep every forced finite residual exactly at
$Z_{r,j,\tau}(\mathbf p_0)$. For each forced infinite residual compute
its valid prefix through $h$ from its finite description. Retain all early
leaves and their absent descendants, put private holes in the unobserved
children of the branches at the boundary, and use one such context for
all occurrences of the same residual name. Each infinite description has
an infinite branch, so its frontier is nonempty. For a hidden residual
choose the prefix of $\Omega$ through $h$. Different original names have
independent frontiers even when their completed values coincide; repeated
names reuse the whole context and filling.

By (PAC.11), after the forced finite coordinates have been inserted, each
companion has a finite seed for its entire negative conjunction at this
same rank tuple. Apply [SLP, Lemma 2.1][SLP] on this normalized Cartesian
piece. It gives one finite tuple with every prescribed infinite prefix and
all negative records together. [SLP, Theorem 3.1 and Corollary 3.2][SLP]
express the same exact support-neighbourhood criterion; here its feasibility
antecedent is furnished by the ray, not assumed for unknown finite values.
No local prefix theorem is reproved. The §2 source reduction and the finite
substitution of §4 verify its full carrier hypothesis at this use.

The actual anchor output uses the same finite ranks and the produced
divergent ranks; by (PAC.8) it agrees with $K(\mathbf c)$ through $h$.
Every companion token does likewise: finite atoms and forced finite
residuals agree exactly, divergent atoms satisfy (PAC.8), and live residuals
have the prescribed prefixes. Nonexpansion of each fixed $\rho^e$ and
pairing then gives agreement of every companion source with $K$ through
$h$. Therefore they share one original four-valued prefix. Soundness of
the exact source covers puts each actual finite output in its entire
$D_r$, with every old and target exterior, partition, literal, sign,
off-task relation and endpoint guard. It is not necessary that the finite
sources satisfy the cross-source completed equalities literally.

All chart tuples, rank modes and matching cases are finite, and every
compiler and semilinear test terminates. A nonempty $G_\tau$ therefore
gives the second alternative with a terminating construction at every
requested $h$. If every $G_\tau$ is empty, the necessity argument gives
$\neg\forall h\,J_B(h)$. To extract $H$, decide $J_B(0),J_B(1),\ldots$
by NSF's fixed-depth multi-source feasibility. For each supplied $h$ one
can enumerate the finitely many valid four-reply prefix patterns and
conjoin one pattern with the entire stratum predicate for every $r$;
NSF decides the resulting finite native queries. The search must stop,
because the preceding finite classification has proved that some $H$
fails. This is a terminating exclusion extraction after a terminating
negative decision, not unsuccessful enumeration of possible contacts.
The alternatives are incompatible by (PAC.5). $\square$

The case of no divergent coordinates is included. Its support test is
ordinary nonemptiness. If $K$ is finite, sufficient agreement isolates that
one source, so distinct complete rows cannot have that contact. The theorem
thus does not create a spurious contact by treating a finite tree as having
a live frontier. Empty residual products and empty negative lists also
retain their literal meanings in URR and SLP.

## 6. Complete acquired consumer with infinitely many contacts

**Definition 6.1 (acquired six-hole input).** Use

$$
W(a,b,z)=\langle a,\langle b,\langle z,z\rangle\rangle\rangle,
\qquad P=\{L,RL,RRL,RRR\}.
\tag{PAC.16}
$$

The old row has entire exterior
$\langle h_1,\langle h_2,\langle h_3,h_4\rangle\rangle\rangle$,
reached set $P$, and partition $\{\{1\},\{2\},\{3,4\}\}$.
Retain the literals $(0,L,\mathsf{branch})$ and
$(0,RL,\mathsf{branch})$. The signed list is exactly

$$
\begin{aligned}
 &(1,LL,0,L,=),\quad (1,RLL,0,RL,=),\\
 &(0,RRL,0,RLR,\ne),\\
 &(1,RRL,0,L,\ne),\quad(1,RRR,0,RL,\ne).
\end{aligned}
\tag{PAC.17}
$$

Every record retains both guards. Use the common public paid acquisition
of Assumption 1.4 with final $N=1$. This successful output is inhabited by
the witnesses below; no fictional acquisition of an impossible output is
asserted. Its full mathematical fibre has no extra source-shape promise.

**Proposition 6.2 (both source directions and exact full rows).** The
entire acquired fibre is

$$
\begin{aligned}
D=\{W(T_{n+2},T_{m+2},z):;& n,m\ge0,\ n\ne m,\\
 &z\ne T_{n+2},\ z\ne T_{m+2},\ z\ne T_m,\\
 &z\ne T_{n+1},\ z\ne T_{m+1}\}.
\end{aligned}
\tag{PAC.18}
$$

Take $Q=\{LL,LR,RLL,RLR,RRL,RRR\}$. All its addresses are reached,
with full exterior

$$
C_Q=\langle\langle h_1,h_2\rangle,
       \langle\langle h_3,h_4\rangle,\langle h_5,h_6\rangle\rangle\rangle
\tag{PAC.19}
$$

and actual hole tuple $(T_{n+1},T_n,T_{m+1},T_m,z,z)$.
Let $r_0$ be the complete label with partition
$\{\{1\},\{2,5,6\},\{3\},\{4\}\}$, and $r_1$ the complete label
with partition $\{\{1\},\{2\},\{3\},\{4\},\{5,6\}\}$.
Their exact entire strata are

$$
\begin{aligned}
D_{r_0}&=\{U_0(n,m):n,m\ge0,\ n-m\notin\{-1,0,1,2\}\},\\
U_0(n,m)&=W(T_{n+2},T_{m+2},T_n),\\
D_{r_1}&=\{U_1(n,m,z):n,m\ge0,\ n-m\notin\{-1,0,1\},\\
 &\hspace{35mm}z\ne T_{n+i},\ z\ne T_{m+i}\ (i=0,1,2)\},\\
U_1(n,m,z)&=W(T_{n+2},T_{m+2},z).
\end{aligned}
\tag{PAC.20}
$$

The difference notation abbreviates finite affine equalities and their
negations over natural $n,m$. Both labels retain (PAC.19) and the whole
reached set. The anchor is residual-free; the companion carrier before its
negatives is the entire $\mathcal T$, with the same $z$ repeated in both
output positions and compared against both rank coordinates.

Proof. An arbitrary source giving the old row has precisely the form
$W(a,b,z)$, with its actual $a,b,z$, and $a,b,z$ pairwise distinct.
Write the branched $a$ as $\langle l,t\rangle$. The first positive
record says exactly $\rho l=\langle l,t\rangle$. This is the existing
native feedback atomicity application of [ARH, Theorem 4.2][ARH]; here is
the parameter correspondence. By the native mass identities of [URR,
Definition 2.1][URR], $\gamma(l)>0$ would make the right side's mass
strictly exceed $\gamma(l)=\gamma(\rho l)$. Thus $l=T_k$; the equality
forces $a=T_{k+1}$, so it is branched only for $k\ge1$. Its actual children
are $T_k,T_{k-1}$ by the recurrence, hence $a=T_{n+2}$ for $n=k-1$.
The second record identically gives $b=T_{m+2}$. No new feedback
classification is being asserted.

At epoch zero $RLR$ now has whole value $T_m$, giving $z\ne T_m$.
The old distinct classes give $n\ne m$, $z\ne T_{n+2}$ and
$z\ne T_{m+2}$. The last two negatives say
$\rho z\ne T_{n+2}$ and $\rho z\ne T_{m+2}$. Since
$T_{n+2}=\rho T_{n+1}$ and $\rho$ is injective, these are exactly the
last two inequalities in (PAC.18). All endpoints are reached: the outer
branches persist, and the recorded child addresses are in the branched
$a,b$. This proves the arbitrary-source direction. Conversely every
finite tuple of (PAC.18) has that old exterior and partition, the two
branch literals, both actual-epoch positive records and all three negative
records with both guards. This gives the other direction on the whole
source fibre.

The tuple at $Q$ follows by the atomic recurrence. In $r_0$, the complete
partition forces $z=T_n$. Distinctness of the other four atomic classes
excludes $n-m\in\{-1,0,1\}$. The old distinctness additionally excludes
$T_n=T_{m+2}$, namely $n-m=2$. All other inequalities in (PAC.18) are
then either automatic or among these exclusions. This gives the first
stratum in both directions. In $r_1$, the four atomic classes are distinct
exactly under $n-m\notin\{-1,0,1\}$. Their inequalities with $z$,
together with (PAC.18), give precisely the six displayed comparisons with
indices $i=0,1,2$. The copied pair of $z$ holes remains one entire class.
Conversely these tests fill (PAC.19) with exactly the required complete
partition and preserve the old row and every retained record. These are
the two exact stratum correspondences. $\square$

**Proposition 6.3 (infinite fixed-parameter family and finite signed
witnesses).** For every fixed $c\ge0$, the two full strata of (PAC.20)
have the common accumulation contact

$$
K_c=W(\Omega,T_{c+2},\Omega).
\tag{PAC.21}
$$

All $K_c$ are distinct, and each has actual finite signed witnesses at every
requested inclusive depth. Their contact construction retains $m=c$
through all depths, the shared residual, and the entire acquired input.

Proof. For supplied $h$ put

$$
m=c,\qquad n=\max(c+3,2h+2),\qquad
Z_0=\alpha,\quad Z_{d+1}=\langle Z_d,Z_d\rangle,
\tag{PAC.22}
$$

and choose the actual finite sources

$$
u_h^0=U_0(n,c),\qquad u_h^1=U_1(n,c,Z_{h+1}).
\tag{PAC.23}
$$

The first uses the same atomic $T_n$ in both copied positions. The second
uses the same finite $Z_{h+1}$ in both positions. The tree
$Z_1=\langle\alpha,\alpha\rangle$ has mass one; positive mass propagates
through its iterated pairs. Thus $Z_{h+1}$ is non-atomic and differs from
every $T_j$, including all six ranks in (PAC.20). Since $n\ge c+3$, all
rank exclusions hold too. Proposition 6.2 gives membership in the two
entire strata, with the exact complete rows, every sign, both guards and
all old classes. This also proves their attainment.

Both $T_n$ and $Z_{h+1}$ branch through depth $h$ by (PAC.8) and the
perfect-tree definition. The finite $T_{c+2}$ is unchanged. Hence both
sources agree with $K_c$ through $h$, including absent replies in its
finite component, and they share one original prefix. Increasing $h$
gives a sequence approaching $K_c$ in each stratum. At address $RL$,
$K_c$ has the entire finite subtree $T_{c+2}$; injective atomic indices
make the contacts distinct for distinct $c$.

Thus infinitely many fixed finite parameters survive, with a correlated
rank difference and repeated companion residual rather than a finite
contact list. These explicit witnesses consume existing atomicity, mass
and depth facts; the new uniform theorem handles the whole parameter family,
not just this chosen section. No negative or row is assigned to $K_c$.
$\square$

## 7. Actual recovery consequences and distinct resource questions

**Corollary 7.1 (uniform new-read obstruction).** Under Assumption 1.4,
a positive contact outcome of Theorem 5.1 excludes every deterministic
source-total static or serial forward service with a uniform finite number
of new raw reads for the entire original target row on $D$. This applies
to the acquired input in §6 at authentic $N=1$.

Proof. Choose any distinct $r,s\in B$. The actual finite witnesses at
every depth disprove determining-prefix existence on the entire $D$.
Consume [ARH, (ARH.2.3)][ARH] at its operational scope. More explicitly,
a controller with at most $K$ actual reads has finitely many realized reply
histories. At each one, common deterministic control fixes its finite
computation and update segment until the next read or halt; source-total
termination makes every realized segment finite. Its finite reply tree
therefore submits finitely many physical words, with a maximum length $h$.
The two witnesses at that $h$ give the same replies at every common actual
epoch by original-prefix locality, including originally absent and born
addresses. They take the same control branches and halt with one output,
contradicting their distinct complete rows. Mathematical description
inversion and witness generation introduce no lawful service port.
$\square$

**Corollary 7.2 (whole-row decision when every pair is covered).** Suppose
the entire exact attained image $R_Q(D)$ is finite, with its exact distinct
row list supplied by [NPL, Theorem 5.3][NPL]. Suppose every pair of distinct
rows has an anchor of Assumption 2.1, or has already been settled by another
applicable exact prefix supplier. Then whole-row uniform-finite-read
existence is decidable: a positive pair contact excludes it; otherwise the
maximum of all pair exclusion depths determines the whole row. Zero or one
attained row is constant and needs zero new reads.

Proof. There are finitely many distinct pairs. A depth excluding a common
prefix for each pair also excludes any row-disagreeing source pair when
all these depths are replaced by their maximum. Conversely a single
positive pair supplies arbitrarily deep disagreements. Apply ARH's
operational equivalence. For more than two selected rows, exclusion of
$J_B(H)$ alone is not enough: two different rows can still share a prefix
while another row is excluded. The complete exact image and all distinct
pairs are therefore necessary in this use. An infinite full-row image is
the separate existing finite-output obstruction of NPL, not a conclusion
from one selected $B$. $\square$

**Proposition 7.3 (a sufficient paid consumer, without an optimum).** Given
a sufficient inclusive $H$ from Corollary 7.2 and authentic $N$, the existing
static original-prefix decoder recovers the target with at most

$$
K_H=2(2^{H+1}-1)\text{ new raw reads},\qquad
\max |p|\le H+\lceil N/2\rceil,\qquad
\sum |p|\le K_H(H+\lceil N/2\rceil),
\tag{PAC.24}
$$

and zero post-entry updates. The read and word bounds are sufficient; no
global minimum, local-time, memory, preparation, installation or retention
bound is asserted.

Proof. For every original address of length at most $H$, use the actual
current-register decoder of [ARH, §2][ARH] and
[DelayedOriginalReadout, `original_decoder_correct` and
`original_decoder_service`][DOR]. Each original reply needs at most two
chronological paid calls of the displayed maximum length, including absence;
there are $2^{H+1}-1$ original words. Every repeated actual call is counted.
Enumerate finite candidate originals and test the whole acquired predicate
and recovered prefix until one passes. The actual source is a candidate,
so this local computation terminates sourcewise; its complete row agrees
with the real source by the determining-prefix property. Output that row
and halt. No candidate is claimed to be the real original.

Before service entry, ARH's public producer traverses each finite acquired
subtree at its actual epoch, pays for all its calls, compares the resulting
finite descriptions, makes the actual forward updates and applies the
stipulated complete state cut. Every finite source satisfying §6's records
produces the same retained state by ARH's two-way correspondence, although
its acquisition lengths may differ. Those sourcewise finite costs are not
refunded by compact signed records. A full original traversal at fixed $N$
also terminates on every finite source but need not have a uniform read
bound. Local search, address generation, working memory, output,
authentication, preparation, installation and complete-successor retention
remain separate charges. No cost comparison uses a sum of coordinate
suprema as a same-run weighted value, and zero weights remain allowed.
$\square$

## 8. Mathematical attribution and remaining domain

**Definition 8.1 (reused results and evidence scope).** The following are
precise suppliers, not independent proofs of the present contact theorem.
The statements in this volume are ordinary mathematical deductions and
are not Lean-kernel verified. The uniform bridge of Lemma 3.2, the exact
cofinal-locus synthesis of Theorem 4.2, and their source-faithful combination
in Theorem 5.1 are `repo-derived`. The consumer and service consequences
are applications with the explicit correspondences of §§6–7; atomicity,
NSF feasibility, NIC covers, URR support, SLP lifting and Presburger
semilinearity are credited existing results, not new versions of them.

| Mathematical source | Exact use and retained boundary |
| --- | --- |
| [ABC, Theorems 2.2–2.3][ABC]; [CAR, Lemma 4.1][CAR] | Finite normal coding, interpreted forward action, and finite arithmetic comparison of residual-free templates. No group action or free inverse observation. |
| [NIC, Theorems 3.2–3.3, Proposition 3.5 and Theorem 4.3][NIC] | Entire mixed signed source covers, arbitrary native pre-negative residual product, and all original source/row directions traced in §2. |
| [NSF, §§2–6][NSF] | Exact finite signed feasibility and supplied-depth multi-source queries. They do not themselves decide unknown contact parameters. |
| [URR, Definition 2.1, Theorem 3.1 and Corollary 3.2][URR] | Native mass, exact simultaneous negative support after finite substitutions; its section is not the whole source image. |
| [SLP, Lemma 2.1, Theorem 3.1 and Corollary 3.2][SLP] | Joint prefix lifting on the exact normalized Cartesian grammar, with finite coordinates fixed and feasibility established. Unknown finite parameters are eliminated here before that application. |
| [NLC, Lemma 3.1 and §§5–6][NLC] | Atomic minimum depth, ordinary completion prefixes, and the distinction between a supplied finite context and an unknown parametric family. |
| [NPL, Theorems 4.1 and 5.3][NPL] | Exact finite/infinite output and full-row image, separately from joint-prefix contacts. |
| [ARH, Assumption 1.3, Proposition 2.1, (ARH.2.3), Theorem 4.2][ARH] | Complete paid acquired input, operational prefix/service correspondence and existing feedback atomicity. |
| [NativeDepthPatterns, `original_prefix_locality`][NDP]; [NativeCutFibers, `legal_values_row`, `rowFiberEquiv`][NCF] | Fixed-epoch prefix locality and entire old-row reconstruction. They do not supply a signed parametric stopping theorem. |
| [NativeHistoryCells, `cell_feasibility_exact`, `historyCellEquiv`][NHC]; [NativeSymbolicRecutting, `symbolic_recut_exact`][NSR] | Owning literal-history cells and full recutting at their stated depth hypotheses. Arbitrary signed native constraints use the ordinary NSF/NIC interfaces, not an extension of these Lean types. |
| [NativeGroundSeparation, `simultaneous_ground_separation`][NGS]; [DelayedOriginalReadout, `original_decoder_service`][DOR] | Finite free-magma separation and paid current-register decoding. Separation alone supplies neither interpreted-$\rho$ density nor contact synthesis. |
| [Ginsburg–Spanier, Theorems 1.2–1.3][GS] | `literature-attested`: arbitrary Presburger sentence decision and effective equivalence with semilinear subsets of $\mathbb N^n$. Applied only to (PAC.11), after the native compiler. |
| [Comon–Lescanne, §6.2][CL] | `literature-attested`: their preceding free-term results do not hold in general nontrivial equational theories. No disunification transfer to interpreted $\rho$ is used. |

The primary arithmetic source is S. Ginsburg and E. H. Spanier,
*Semigroups, Presburger Formulas, and Languages*, Pacific Journal of
Mathematics 16(2) (1966), 285–296. Theorems 1.2–1.3 concern nonnegative
integer Presburger formulas, including quantification and effective
semilinear descriptions; these are exactly the arithmetic domain and
operations of §4. The comparison source is H. Comon and P. Lescanne,
*Equational Problems and Disunification*, Journal of Symbolic Computation
7 (1989), 371–425, DOI 10.1016/S0747-7171(89)80017-3. Its §6.2 expressly
separates the preceding free-term results from general nontrivial
equational theories. It supplies a transfer boundary, not a native solver.

The owning D5 interfaces include the private reconstruction helpers
`recover_fill`, `fill_injective`, `classValue_distinct`, `syntax_iff_ground`,
`sourceCell_right`, `cellSource_injective`, `termAt_fill`, `exterior_commute`,
`compound_mass_ne`, `present_label_decode`, and `original_query_bounds`.
Their domain restrictions remain attached to their public consumers; they
are not treated as missing results or as proofs of the new ordinary
parametric bridge. The relevant overlap boundary is explicit: [FJC,
Definitions 2.1–2.4 and Theorem 4.2][FJC] concerns its certified rank-free
functional presentation. Theorem 5.1 imposes neither that presentation nor
a finite list of completed contacts on its companions. SLP owns the local
Cartesian prefix theorem consumed here. No external priority or general
impossibility claim follows from these comparisons.

**Open problem 8.2 (anchorless stopping).** Give a source-faithful
terminating exclusion-or-realization choice for arbitrary complete acquired
signed input when no exact atomic-output full-row anchor is available.
The missing obligation is an effective complete search for common output
contacts of residual-visible nonfunctional source maps, with their
finite barriers and joint supports, together with actual finite signed
lifting. The finite generalized description of Lemma 3.2 is supplied by
an atomic anchor and does not exhaust arbitrary residual-visible limits.
Positive residual or navigation restrictions in a differently supplied
piece must also be preserved or eliminated in both directions before SLP
applies. A supplied-depth test, a fixed finite context checker or a section
is not this missing all-depth choice. No undecidability, intrinsic anchor
recognition, general resource optimum or completion of that larger
research objective is asserted.

[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[CAR]: RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_ATOMIC_RECOVERY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[FJC]: RECURSIVE_RELATIONAL_OBSERVATION_FUNCTIONAL_JOINT_CONTACT.md
[NDP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[NCF]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[NHC]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[NSR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[NGS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[DOR]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf

## 追加锚（本行以下为增补区）
