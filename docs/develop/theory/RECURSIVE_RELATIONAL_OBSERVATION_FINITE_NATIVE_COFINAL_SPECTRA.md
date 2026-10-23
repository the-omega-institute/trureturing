# Finite-native cofinal spectra for source-faithful joint prefixes

> This generic-v1 volume is ordinary mathematical reference input. It uses the
> supplier material at revision '5c920a039f074b6274e8a033ea9c99b556e4c86a' as
> fallible repository evidence. No Lean, Blueprint, registry, compilation or
> frozen-status claim is made here. The complete acquired-source correspondence
> keeps arbitrary old and target cuts. Its cofinal contact criterion does not
> decide the unknown completed-contact problem.

## 1. Native source, acquired input and the joint question

**Definition 1.1 (finite native trees).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,
&\rho\beta&=\langle\beta,\alpha\rangle,
&\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle,\\
T_j&=\rho^j\alpha\qquad(j\in\mathbb N).
\end{aligned}
\tag{FNS.1}
$$

Every source is a nonempty finite free ordered tree. The displayed laws
interpret \rho; it is not a free unary constructor. An address is a word in
$\{L,R\}$, with the root $\varepsilon$. The four-valued reply at an address is
the corresponding leaf, branch, or absence. Write $u\equiv_h v$ when all
replies at addresses of length at most $h$ agree. Repeated occurrences of one
name always denote one source subtree; sharing a value does not delete an
occurrence from the ordered source.

**Definition 1.2 (complete acquired fiber).** An attained acquired input is

$$
I=(P,R,H_0,H_{\rm rel},Q,N).
\tag{FNS.2}
$$

Here $P$ and $Q$ are the original finite prefix-free cuts, $R$ is the complete
old row (concrete exterior, reached set and full equality partition), $H_0$
contains all literal records, and $H_{\rm rel}$ contains every whole-subtree
equality or disequality record together with its actual epoch. For a finite
original source $u$, let

$$
D=\{u:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{FNS.3}
$$

A signed record $(e,p,f,q,\bowtie)$ is interpreted as

$$
p\in\operatorname{Pos}(\rho^e u),\quad
q\in\operatorname{Pos}(\rho^f u),\quad
(\rho^e u)|_p\ \bowtie\ (\rho^f u)|_q,
\tag{FNS.4}
$$

with both endpoint guards required for either sign. Repetitions, old
off-task constraints, cross-class inequalities and all recorded epochs remain
in (FNS.3); absence is never silently changed into a disequality.

For a complete attained row $r$, put

$$
D_r=\{u\in D:R_Q(u)=r\}.
\tag{FNS.5}
$$

If $B$ is a finite set of at least two distinct attained complete rows, define

$$
J_B(h)\Longleftrightarrow
\exists (u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\;(u_r\equiv_h u_s).
\tag{FNS.6}
$$

The tuple in (FNS.6) consists of alternative originals, one satisfying each
whole row. It is not one source carrying contradictory labels and it is not a
collection of unrelated pairwise witnesses.

**Assumption 1.3 (paid producer and authentic continuation).** The producer
has the source-total paid interface of [ARH, Assumption 1.3 and Proposition
2.1][ARH]. It acquires $R$ and every listed whole endpoint at its actual epoch,
retains all guards and signs, advances one original-root register to an
authentic $N$ at least every recorded epoch, and exposes the complete
accessible-state cut. Its successful retained state has exactly the fiber
$D$. Subsequent actual actions are paid four-valued original-root reads and
serial forward applications of $\rho$ on that same register.

This is a premise about the producer and accessible-state factoring. A
mathematical source chart, rank, equality test, selected-source witness,
reset, reroot, clone, clock, original-version read or inverse is not an
additional observer port. Acquisition, actual reads, updates, words,
computation, installation, retention and output remain separate resources.

## 2. Exact finite profiles and the cofinal spectrum

**Definition 2.1 (a mixed source chart).** A chart piece $b$ has dimensions

$$
\mathbf c\in\mathbb N^k,\qquad
\mathbf w\in\mathbb N^q,\qquad
\mathbf f\in\mathcal T^p,\qquad
\mathbf z\in\mathcal T^m.
\tag{FNS.7}
$$

The coordinates $\mathbf c$ are finite atomic coordinates held fixed in a
profile, $\mathbf w$ are the coordinates allowed to escape to infinity,
$\mathbf f$ are arbitrary finite **original** trees retained as finite
barriers, and $\mathbf z$ are unrestricted Cartesian finite residuals. The
chart supplies a finite mixed native source map

$$
U_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z)
\tag{FNS.8}
$$

and a Presburger rank condition $P_b(\mathbf c,\mathbf w)$. Its signed
condition is one finite conjunction

$$
\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z)
 =\bigwedge_{\ell=1}^{s_b}
 A_{b,\ell}(\mathbf c,\mathbf w,\mathbf f,\mathbf z)
 \ne B_{b,\ell}(\mathbf c,\mathbf w,\mathbf f,\mathbf z),
\tag{FNS.9}
$$

where every side is a mixed native expression built from finite grounds,
$T_{n+d}$, fixed powers of $\rho$, ordered pairing, and the shared names in
(FNS.7). The complete list, including repeated names and repeated
inequalities, is retained. There is no hidden positive residual equation or
image restriction in the Cartesian $\mathbf z$ coordinates.

**Definition 2.2 (entire finite-profile support).** For supplied finite
$(\mathbf c,\mathbf f)$ define

$$
S_b(\mathbf c,\mathbf f)=
\{\mathbf w:P_b(\mathbf c,\mathbf w)\land
 \exists\mathbf z\in\mathcal T^m\;\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z)\}.
\tag{FNS.10}
$$

The exact cofinal spectrum is

$$
\Xi_b(\mathbf c,\mathbf f)\Longleftrightarrow
\forall M\in\mathbb N\;\exists\mathbf w,\mathbf z\quad
\left[
\begin{array}{l}
P_b(\mathbf c,\mathbf w)\land
\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z),\\
\displaystyle\bigwedge_{j=1}^{q}w_j\ge M
\end{array}\right].
\tag{FNS.11}
$$

Thus $\Xi_b$ is a diagonal cofinality statement, not coordinatewise
unboundedness. The same finite $\mathbf c$ and the same finite original
tuple $\mathbf f$ occur before every $M$. If $q=0$, the empty rank tuple is
the unique tuple and the lower-bound conjunction is true. If $m=0$, the
residual tuple is the unique empty tuple. If $p=0$, $\mathbf f$ is the
unique empty finite profile. If $k=0$, $\mathbf c$ is the unique empty
scalar complement. These conventions include all zero-dimensional edges.

**Theorem 2.3 (terminating exact spectrum compiler).** For every chart $b$
and every supplied finite original tuple $\mathbf f$, there is a terminating
construction of a Presburger formula
$\widehat\Xi_{b,\mathbf f}(\mathbf c)$ such that

$$
\widehat\Xi_{b,\mathbf f}(\mathbf c)\quad\Longleftrightarrow\quad
\Xi_b(\mathbf c,\mathbf f).
\tag{FNS.12}
$$

The compiler retains $\mathbf f$ as the original finite tuple supplied to the
chart. It does not enumerate a catalogue of finite trees and does not replace
the tuple by separator markers.

**Proof.** This is an algebraic compiler on the declared Cartesian chart;
its acquired-source use requires the separate exact image correspondence in
Sections 3--4. For the fixed finite tuple $\mathbf f$, expand its finite
syntax as ground native trees. The resulting negative list is in the mixed
grammar of [URR, Definition 1.2][URR], with scalar variables
$(\mathbf c,\mathbf w)$ and Cartesian residual variables $\mathbf z$.

[URR, Theorem 3.1 and Corollary 3.2][URR] construct one finite tuple
$\mathbf z^\star_{b,\mathbf f}$ such that, for every scalar assignment,

$$
\exists\mathbf z\;\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z)
\Longleftrightarrow
\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z^\star_{b,\mathbf f}).
\tag{FNS.13}
$$

The conjunction is handled jointly: one tuple breaks every nonidentity
equality, rather than one residual witness per conjunct. Native mass separates
residual-containing compounds from residual-free terms, and the native clock
separates the finitely decorated repeated residual names; interpreted $\rho$
is never treated as a free unary constructor.

After substitution by $\mathbf z^\star_{b,\mathbf f}$, [URR, Corollary
3.2] and the scalar-preserving part of [NSF, Theorem 4.3][NSF] give an exact
Presburger formula $\Psi_{b,\mathbf f}(\mathbf c,\mathbf w)$ for

$$
P_b(\mathbf c,\mathbf w)\land
\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z^\star_{b,\mathbf f}).
\tag{FNS.14}
$$

Set

$$
\widehat\Xi_{b,\mathbf f}(\mathbf c):\Longleftrightarrow
\forall M\;\exists\mathbf w\;
\left(\Psi_{b,\mathbf f}(\mathbf c,\mathbf w)
\land\bigwedge_j w_j\ge M\right).
\tag{FNS.15}
$$

Presburger quantifier elimination terminates and proves (FNS.12). The
construction is exact for every supplied finite $\mathbf f$; it is not an
enumeration of possible $\mathbf f$ and it does not assert that all finite
profiles have one common arithmetic formula independent of their native
syntax. $\square$

**Theorem 2.4 (finite-profile feasibility and synthesis).** If
$\Xi_b(\mathbf c,\mathbf f)$ holds, then for every $M$ the compiler extracts
one $\mathbf w$ with all $w_j\ge M$ and one finite $\mathbf z$ satisfying the
entire conjunction (FNS.9). The source
$U_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z)$ is a finite native witness. If
$\Xi_b(\mathbf c,\mathbf f)$ fails, some finite $M$ excludes every such source
with that fixed $(\mathbf c,\mathbf f)$.

**Proof.** Presburger witness extraction applied to (FNS.15) supplies the
single simultaneous rank tuple. The URR section (FNS.13) supplies one finite
residual tuple satisfying all whole disequalities together; evaluation of
(FNS.8) preserves every shared occurrence. For an exact acquired chart, its
source correspondence additionally preserves every original signed guard.
The converse is projection
of any finite source witness. Negating (FNS.11) gives the finite bound in the
second statement. No uniform source-size, source-depth or read-cost bound
follows. $\square$

**Corollary 2.5 (joint support and selected marginal witnesses).** Replacing
(FNS.11) by separate unboundedness assertions for each rank coordinate can
change its truth value: the support $w_1=0\lor w_2=0$ is unbounded in each
coordinate but never meets both positive lower bounds. A valid spectrum
retains one tuple satisfying every coordinate lower bound at once.

At fixed $(\mathbf c,\mathbf w,\mathbf f)$, URR gives a more specific fact
for this unrestricted Cartesian negative-only grammar:

$$
\exists\mathbf z\;\bigwedge_\ell A_\ell\ne B_\ell
\quad\Longleftrightarrow\quad
\bigwedge_\ell\exists\mathbf z_\ell\;(A_\ell\ne B_\ell).
\tag{FNS.15a}
$$

**Proof.** The forward implication is projection. For the reverse implication
no listed equality is a residual identity, so URR's one section breaks all
of them together, including shared names. Separately selected per-clause
fillings need not themselves assemble into that single tuple; this is a
witness-assembly warning, not a failure of (FNS.15a). Positive residual
restrictions would require a different argument and are excluded from this
carrier. $\square$

**Corollary 2.6 (parametric finite templates).** The same compiler applies
when a finite coordinate is a mixed native template $f_i(\mathbf c)$ rather
than a ground tree fixed independently of $\mathbf c$. In that case it
produces one Presburger formula in $(\mathbf c,\mathbf w)$ for

$$
P_b(\mathbf c,\mathbf w)\land
\exists\mathbf z\;\Delta_b(\mathbf c,\mathbf w,
                    \mathbf f(\mathbf c),\mathbf z).
\tag{FNS.16a}
$$

This is the uniform arithmetic step used later in (FNS.25); it does not
enumerate the values of $\mathbf c$.

**Proof.** Leave the designated atomic ranks in $\mathbf c$ as scalar
variables while expanding the finite template $\mathbf f(\mathbf c)$.
The mass-and-clock construction in [URR, Theorem 3.1][URR] depends only on
the finite syntax and on the number of residual decorations, not on the
values of atomic ranks. Its single residual tuple therefore works for all
$(\mathbf c,\mathbf w)$ at once. The scalar-preserving branch construction
of [NSF, Lemma 5.1 and Theorem 4.3][NSF] then yields a finite Presburger
projection. Substitution of the same template in every repeated occurrence
preserves the original shared-coordinate relation. $\square$

## 3. Exact whole-source strata and a common completed map

**Theorem 3.1 (connection to exact existing strata).** Suppose a finite family
of chart pieces $b$ is an exact NIC signed image cover of an acquired row
stratum. Then its source set is exactly

$$
\bigcup_b\{U_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z):
P_b(\mathbf c,\mathbf w)\land
\Delta_b(\mathbf c,\mathbf w,\mathbf f,\mathbf z)\},
\tag{FNS.16}
$$

with both inclusions taken over finite original sources. The complete old
exterior, reached set, equality partition, all off-task records and all
whole signed inequalities are retained jointly by the source maps and their
rank/negative predicates; positive identifications are built into the maps.

**Proof.** NIC's expansion and finite-shape normalization give the forward
inclusion from chart parameters to a source satisfying the old row and every
record. Its completeness direction reads the actual finite ranks, finite
frontier trees and repeated residual values from an arbitrary source and
reconstructs that same source. Applying its signed pullback keeps every
whole-tree disequality. A rank projection or a URR section alone would prove
only existence at a rank; (FNS.16) uses the full source map and therefore has
both directions. $\square$

The existing finite-depth feasibility, finite whole-row image, supplied-prefix
closure and equality-of-supplied-description results are used only under their
published hypotheses. Recognizing one of those certificates does not prove
completeness of this chart family or synthesize a common completed contact.

**Definition 3.2 (completion and common-map obligation).** Let
$\widehat{\mathcal T}$ be the finite-prefix completion of native trees and let
$\Omega$ be the all-branch tree. A completed source map is obtained from
(FNS.8) by replacing a divergent atomic sequence $T_{w_j}$ by $\Omega$ and
by taking finite-prefix limits of residual coordinates. Finite signs and
finite row partitions are interpreted only on finite sources; no sign is
assigned to a completion point.

For a tuple of row pieces $\mathbf b=(b_r)_{r\in B}$, a **common completed
map certificate** consists of:

1. a finite mode for each piece's scalar coordinates, with a fixed finite
   complement $\mathbf c_r$ and the other coordinates set to $\infty$;
2. a completed residual tuple $\boldsymbol\eta_r$ for each piece, with its
   finite coordinates retained as their actual native values $\mathbf f_r$;
3. the continuous extension $\widehat U_{r,b_r}$ of every exact source map,
   and a proof that all its completed outputs are one common original tree.

Coordinates of different alternative sources are independent unless the
common-output equations prove a relation between them. Within each source,
all repeated names retain the same value. Thus a common completed output does
not require unrelated charts to have identical residual coordinates. Finite
profiles precede all depths and lower bounds. Effective prefix synthesis from
a certificate additionally requires computable finite prefixes of its
completed values; an arbitrary existence proof supplies no runtime port.

**Lemma 3.3 (finite-coordinate graph lemma for the recognized map).** Consider
a functional system with at most one definition per state, obtained after
fixing a scalar mode $A$ and finite complement $\mathbf c$. Normalize fixed
powers through explicit pairs and grounds. Build the finite root-link graph:
an edge $i\to j$ of weight $a\ge0$ records $Y_i=\rho^aY_j$. Every remaining
recursive occurrence is required to lie below an explicit ordered pair.

Under these guard conditions one can compute a set $F_A$ and mixed native
templates $f_i^A(\mathbf c)$ such that every completed solution has the same
value $f_i^A(\mathbf c)$ on each forced finite coordinate $i\in F_A$. Every
other canonical coordinate is assigned an infinite-prefix representative;
its finite prefixes are computable. A malformed graph or an unguarded
residual occurrence is outside this lemma, not a negative answer.

**Proof.** Collapse each strongly connected component of the root-link graph.
A cycle with positive total $\rho$-weight cannot contain a finite tree: each
iteration raises the minimum finite-leaf depth, while a finite tree has a
last leaf. It therefore has only the all-branch completion. A zero-weight
cycle is a free state; assign it the all-branch representative. This is a
choice for the completed positive equations only. Its finite signed witnesses
still require the fixed-profile support test and SLP lifting; no negative
condition is asserted on that all-branch representative.

For acyclic root links, substitute along the unique finite path, accumulating
the weight. What remains is a finite system in which every recursive
occurrence is below a pair. Simultaneous unfolding gains one original-prefix
level at each such pair. The finite-prefix contraction argument of [FJC,
Theorems 3.1 and 5.1][FJC] therefore gives one completion for each free
state. Reverse topological evaluation identifies exactly the coordinates
whose values are finite mixed templates in $\mathbf c$; these are $F_A$ and
$f_i^A(\mathbf c)$. A cycle containing a pair cannot be finite: native
leaf count does not decrease under $\rho$, and an occurrence below a pair has a nonempty sibling.
Each cycle edge would strictly decrease finite leaf count, which is impossible.

The graph is finite, so the SCC decomposition, path substitution and finite
template evaluation terminate. The result classifies the finite barriers that
must be fixed before prefix lifting; it does not enumerate arbitrary finite
residual trees. $\square$

**Remark 3.4 (why the finite profile is retained).** A finite coordinate
forced by the graph is inserted as the actual native tree $f_i^A(\mathbf c)$
in every whole negative. A coordinate not forced finite remains a Cartesian
residual for the purpose of SLP lifting, even though its selected completion
representative is infinite. This separation prevents a finite barrier from
being replaced by an infinite marker and prevents an infinite coordinate from
being replaced by a finite catalogue.

## 4. Complete acquired normalization and the installed switching maps

**Definition 4.1 (old classes before source installation).** Keep the supplied
$P,R,Q,H_0,H_{\rm rel},N$ of (FNS.2), with no restriction on the old partition.
Let $C_R$ be the concrete old exterior, let $I_R$ be its reached holes, and
let $\pi_R$ be their full partition. For one variable $v_C$ per old class,
form

$$
L_R(\mathbf v)=C_R[(v_{[p]})_{p\in I_R}],\qquad
D_R^{\rm old}(\mathbf v)=\bigwedge_{C\ne C'}v_C\ne v_{C'}.
\tag{FNS.17a}
$$

The occurrence list is retained: equal classes share a value at every old
hole, while different classes stay unequal. The attained geometry of $C_R$
preserves the reached set and every absent old address under arbitrary finite
fillings. Empty cuts and zero old classes have their literal meanings; if
there are no holes $L_R$ is the whole fixed original tree.

By [ARH, Definition 1.1 and (ARH.1.2)][ARH], equivalently
`NativeCutFibers.rowFiberEquiv` and `legal_values_row`,
$\{u:R_P(u)=R\}$ is exactly the image of (FNS.17a). The inverse reads the
actual old class values from the same original $u$. The owning private
`recover_fill` proves reconstruction of that original, and `classValue_distinct`
proves the required cross-class inequalities. These are mathematical source
maps; the inverse is not a runtime subtree-read port.

**Lemma 4.2 (complete acquired-source normalization).** For every input
(FNS.2), and for every supplied complete original $Q$-row $r$, one can
construct finite families of mixed maps and predicates such that

$$
\begin{aligned}
D&=\bigcup_{b\in\mathcal B_I}
 \{U_b(\mathbf n,\mathbf z):P_b(\mathbf n)\land\Delta_b(\mathbf n,\mathbf z)\},\\
D_r&=\bigcup_{b\in\mathcal B_{I,r}}
 \{U_{r,b}(\mathbf n,\mathbf z):
       P_{r,b}(\mathbf n)\land\Delta_{r,b}(\mathbf n,\mathbf z)\}.
\end{aligned}
\tag{FNS.21a}
$$

Before each negative conjunction, its residual carrier is the full Cartesian
product of finite native trees. Every old positive identification, concrete
exterior, reached/absent fact, literal and positive record is already true on
the source map whenever $P_b$ holds. The entire remaining native negative
list, including off-task old comparisons, is in $\Delta_b$. Both inclusions
in (FNS.21a) reconstruct original sources; an empty family denotes the empty
source set. No assumption that $P$ is the root cut or the target cut is made.

**Proof.** This is the acquired instantiation of [NIC, Theorems 3.2--3.3 and
4.3][NIC]. The following construction specifies its old-class and target
correspondence. Start with (FNS.17a). Choose an original-prefix depth larger
than all listed cut and endpoint lengths. Refine each old class value by a
finite native prefix pattern with independent frontier variables. Repeated
old occurrences use the same pattern and the same frontier tuple. There are
finitely many such patterns; actual class values select their actual patterns
and actual frontier subtrees. Filling them in $L_R$ returns the same original
source. Early leaves retain their absent descendants.

At every fixed actual epoch, distribute $\rho$ through original branch
nodes. Navigation to a listed endpoint either reaches a mixed expression in
the frontiers, reaches a subtree of an explicitly expanded early leaf, or is
absent. The chosen depth ensures that no listed address enters an unspecified
frontier. Decide all literal replies and both endpoint guards in each case;
an absent endpoint rejects either signed record. Keep every surviving whole
positive or negative comparison at its recorded epochs, including repeats.

For the target, check its entire reached set and form the mask by replacing
exactly those reached $Q$ subtrees by $\alpha$. Equality of this mask to the
concrete mask of $r$ preserves its entire exterior, including uncut frontier
subtrees. For every pair of reached target holes, retain the positive equality
or negative comparison specified by its full partition. Old within-class
equalities are already literal sharing in $L_R$; all distinct-old-class
comparisons in (FNS.17a) remain negative tests. No comparison is selected by
whether it is relevant to $Q$.

Each surviving finite case now has one native source term $W(\mathbf x)$,
a finite positive presentation $\mathscr E(\mathbf x)$ and the full native
negative list $\Delta(\mathbf x)$. Declare every frontier and definitional
auxiliary, even if it is not used in the output. Apply NIC's positive image
construction to $\mathscr E$ alone. Its finite smart-pair cases, free-shape
factorization, scalar equations and connected offset blocks produce
$F_b(\mathbf n,\mathbf z)$ on
$\{\mathbf n:P_b(\mathbf n)\}\times\mathcal T^{m_b}$, with no residual
positive predicate. The sound ambient expansion and the reconstruction of
actual normal codes are the two directions of [NIC, Theorem 3.2]. In
particular dropping ambient normality creates overlapping native images,
not extra positive solutions. This is why no native equality is silently
left to a negative-only separator.

Set $U_b=W\circ F_b$ and pull back every original negative through $F_b$,
evaluating it after native expansion, as required by NIC Theorem 3.3. Fixed
powers distribute through the resulting maps, so their syntax and all
negative sides have (FNS.9)'s mixed form. Forward, each parameter tuple gives
one finite source with the old row, all records and, where imposed, exactly
$r$. Reverse, any source in $D$ or $D_r$ supplies its actual old class values,
prefix pattern, frontiers and named subexpressions. NIC reconstructs that
whole tuple; hence $W\circ F_b$ reconstructs that same source. The actual
old partition, target partition, masks, guards, signs and epochs all survive
both inclusions. All branches are finite and each supplier construction
terminates. This proves (FNS.21a), without selecting a URR section as the
source image. $\square$

**Definition 4.3 (installed switching maps with an arbitrary old row).**
Choose integers $k\ge1,m\ge2$, an installed finite ordered context $C$, and
its prefix-free role frontier

$$
Q=\{p_{A_j}:1\le j\le k\}\cup
  \{p_{X_i},p_{Y_i},p_{Z_i}:1\le i\le m\}.
\tag{FNS.17}
$$

Here $P$ is still the arbitrary supplied old cut; the context $C$ is installed
by actual literals and is not asserted to be the old exterior $C_R$.
At $A_j$ retain its branch literal and the guarded record

$$
(1,p_{A_j}L,\ 0,p_{A_j},\ =).
\tag{FNS.18}
$$

Each payload $E_i(\mathbf n,\mathbf y)$ is built from finite grounds,
$T_{n_j+d}$, fixed $\rho$ powers of $Y$ roles and pairs. Install its displayed
pairs and grounds by literals. A token $\rho^aY_\ell$ at position $q$ is
linked by

$$
(0,p_{Z_i}q,\ a,p_{Y_\ell},\ =),
\tag{FNS.19}
$$

and a token $T_{n_j+d}$ is linked to $A_j$'s right child at epoch $d$.
Unknown tokens are not traversed by the installation skeleton. Additional
finite records and the full old row remain part of the same input.
The installation alone has raw source map

$$
U(\mathbf n,\mathbf x,\mathbf y)
 =C[A_j:=T_{n_j+2},\ X_i:=x_i,\ Y_i:=y_i,\ Z_i:=E_i(\mathbf n,\mathbf y)].
\tag{FNS.20}
$$

Indeed [ARH, Application 26.1][ARH] applied to (FNS.18) gives uniquely
$A_j=T_{n_j+2}$ and its right child $T_{n_j}$. Payload induction gives
$E_i$ using exactly (FNS.19) at its actual epochs. Conversely the atomic
recurrence and payload induction verify every installed record and guard.
This proves the installation map, before imposing the old row.

Let $\Gamma_R(\mathbf n,\mathbf x,\mathbf y)$ be the **entire** pullback
$R_P(U)=R$ together with all additional retained records. In particular it
contains every old within-class equality as well as every cross-class
inequality, exterior/reach fact and signed comparison. Then the exact whole
fiber is

$$
D=\{U(\mathbf n,\mathbf x,\mathbf y):
       \Gamma_R(\mathbf n,\mathbf x,\mathbf y)\}.
\tag{FNS.21}
$$

The predicate $\Gamma_R$ can contain positive residual equations. It is
never passed unchanged to URR or SLP. Lemma 4.2 instead normalizes the full
acquired predicate, including these positives, to (FNS.21a). Atomic ranks
may thereby be reparameterized; the raw installation coordinates are not
silently reused as if normalization had left them independent.

**Theorem 4.4 (exact full switching strata).** For
$\sigma\in\{0,1\}^m$, let $r_\sigma$ have exterior $C$, reached set $Q$
and the complete partition

$$
X_i=\begin{cases}Y_i,&\sigma_i=0,\\ Z_i,&\sigma_i=1,\end{cases}
\qquad\text{all other classes distinct}.
\tag{FNS.22}
$$

Let $\Theta_\sigma$ be (FNS.20) after these simultaneous substitutions, and
let $\Lambda_\sigma$ be every cross-class inequality of this full partition.
Then both exact descriptions are

$$
\begin{aligned}
D_{r_\sigma}
 &=\{\Theta_\sigma(\mathbf n,\mathbf y):
       \Gamma_R(\mathbf n,\mathbf x^\sigma(\mathbf n,\mathbf y),\mathbf y)
       \land\Lambda_\sigma(\mathbf n,\mathbf y)\}\\
 &=\bigcup_{b\in\mathcal B_{I,r_\sigma}}
   \{U_{r_\sigma,b}(\mathbf a,\mathbf z):
       P_{r_\sigma,b}(\mathbf a)\land\Delta_{r_\sigma,b}(\mathbf a,\mathbf z)\}.
\end{aligned}
\tag{FNS.23}
$$

The second line, not the potentially positive first-line predicate, is the
Cartesian negative chart used by Section 2.

**Proof.** In the first line the substitution makes precisely the target
within-class equalities literal; $\Lambda_\sigma$ keeps every other target
comparison. The complete $\Gamma_R$ retains the entire original input,
including old positives. Thus every image point has both the old row and
$r_\sigma$. Conversely a source in $D_{r_\sigma}$ is recovered by the raw
installation map with its actual ranks and $Y$ values; its complete target
partition forces the substitutions and all $\Lambda_\sigma$ tests. The old
predicate still holds on that same source. These prove the first equality.
Lemma 4.2 proves the second equality in both directions.

No old equality is presumed redundant. For example, if $P=Q$ and $R$ fixes
$X_i=Y_i$, a target row requiring $X_i=Z_i$ and $Y_i\ne Z_i$ has empty
stratum. More generally when $P=Q$, $D_r=\varnothing$ for every $r\ne R$.
With $P=\{\varepsilon\}$ the singleton old class places no identification
on different descendant role slots. These are two different admitted old
inputs, handled by the same complete correspondence, not interchangeable
boundaries. Attainment is checked on the full predicates. $\square$

## 5. Exact joint cofinal contact over the complete input

Keep any input (FNS.2) and any supplied finite set $B$ of distinct attained
complete $Q$-rows. Use the full normalized covers in (FNS.21a), allowing
every piece its own dimensions and independent parameter names across rows.
For each piece, compactify its scalar domain to
$\overline{\mathbb N}^{k_b}$, where
$\overline{\mathbb N}=\mathbb N\cup\{\infty\}$, finite values are isolated
and neighborhoods of $\infty$ are lower bounds. Complete residual trees in
$\widehat{\mathcal T}$. The continuous extended map
$\widehat U_{r,b}$ replaces $T_{\infty+d}$ by $\Omega$; it evaluates pairs
and fixed powers by their native completed laws.

**Definition 5.1 (joint profile and common output).** Choose one piece $b_r$
per $r\in B$, scalar divergence sets $A_r$, a finite complement
$\mathbf c_r$, and residual completions $\boldsymbol\eta_r$. Let $F_r$ be
exactly their finite residual coordinates and put
$\mathbf f_r=(\boldsymbol\eta_r)_{F_r}$. Every other coordinate of
$\boldsymbol\eta_r$ has an infinite branch. Write
$\lambda_r=(\mathbf c_r,\infty_{A_r})$. The common-output equation is

$$
\widehat U_{r,b_r}(\lambda_r,\boldsymbol\eta_r)=v
\qquad(r\in B)
\tag{FNS.24}
$$

for one original completed tree $v$. There is no assertion of a finite row
partition or a signed record at $v$. Within each finite source the full
original record list still shares one source.

For the fixed finite profile define

$$
\Psi_r(\mathbf c_r,\mathbf w_r,\mathbf f_r)
\Longleftrightarrow
P_{r,b_r}(\mathbf c_r,\mathbf w_r)\land
\exists\mathbf z_r\;
\Delta_{r,b_r}(\mathbf c_r,\mathbf w_r,\mathbf f_r,\mathbf z_r).
\tag{FNS.25}
$$

Here $\mathbf z_r$ comprises the remaining Cartesian residuals. Section 2
and [SLP, Corollary 3.2][SLP] give its exact Presburger compiler for every
supplied finite original $\mathbf f_r$. Group all finite scalar coordinates
as $\mathbf c=(\mathbf c_r)_{r\in B}$ and all finite trees as
$\mathbf f=(\mathbf f_r)_{r\in B}$. The arithmetic cofinal locus is

$$
\mathcal G_{\mathbf b,\mathbf A,\mathbf F,\mathbf f}
 =\left\{\mathbf c:
 \forall M\;\exists(\mathbf w_r)_{r\in B}\;
 \left[\bigwedge_{r\in B}\Psi_r(\mathbf c_r,\mathbf w_r,\mathbf f_r)
 \land\bigwedge_{r\in B}\bigwedge_{j\in A_r}w_{r,j}\ge M\right]\right\}.
\tag{FNS.26}
$$

The same $(\mathbf c,\mathbf f)$ precedes every $M$ and depth. Each row's
ranks may differ; forcing equality of different rows' ranks or residuals
would change the input. With the product chart, (FNS.26) is exactly the joint
spectrum (FNS.11), with the entire negative conjunction retained. It leaves
all finite original profiles in scope, not a finite profile catalogue.

**Theorem 5.2 (both acquired joint-prefix directions).** For every complete
input and finite attained $B$ as above,

$$
\forall h\;J_B(h)\quad\Longleftrightarrow\quad
\exists\mathbf b,\mathbf A,\mathbf F,\mathbf c,\mathbf f,
       (\boldsymbol\eta_r)_{r\in B},v\quad
 [\text{(FNS.24) and }\mathbf c\in
       \mathcal G_{\mathbf b,\mathbf A,\mathbf F,\mathbf f}],
\tag{FNS.27}
$$

where the residual completions have finite part exactly $\mathbf f$ as in
Definition 5.1. A common completed output is separately required, in addition
to cofinal arithmetic support. When these conditions hold, every requested
finite depth has actual finite signed witnesses from the original full
strata. This is an exact existence criterion; it does not decide or synthesize
the existentially unknown completed outputs or finite profiles.

**Proof (necessity).** For each increasing $h$ choose a tuple witnessing
$J_B(h)$. Lemma 4.2 supplies parameters for that same original source in each
row. There are finitely many chart choices, so pass to an unbounded-depth
subsequence with one tuple $\mathbf b$. The finite-prefix completion is
compact: there are finitely many reply patterns at each depth, and a diagonal
subsequence gives compatible prefixes of one finite or infinite full native
tree. The scalar compactification is compact as well: an integer sequence
has a constant subsequence or a subsequence tending to infinity. These
arguments apply to the finite product of all row parameter spaces. Pass to
one convergent joint parameter subsequence with limits
$(\lambda_r,\boldsymbol\eta_r)$.

Each finite scalar limit is eventually its fixed $c_{r,j}$, and each finite
residual limit is eventually its actual $f_{r,i}$, because finite native trees
are isolated. All other residual limits have infinite branches. The mixed
maps are continuous: pairs gain one prefix level, fixed $\rho$ powers are
prefix nonexpanding, and $T_n\to\Omega$ since every two updates increase the
minimum finite-leaf depth. Thus their output limits agree. Indeed the source
outputs agreed through increasing depths before taking the subsequence.
This proves the one common source equation (FNS.24).

For each $M$, choose a subsequence term past stabilization of all finite
coordinates and above $M$ in every divergent coordinate. The original finite
parameter tuples still satisfy every $P_{r,b_r}$ and the complete
$\Delta_{r,b_r}$. They therefore supply the single joint tuple in (FNS.26).
The same finite original profiles were fixed before every $M$. This proves
the right side of (FNS.27).

**Proof (sufficiency).** First take the common completed-map proof (FNS.24).
For a requested $h$, continuity of its finite mixed maps supplies finite
prefix requirements on every infinite residual coordinate and one finite
simultaneous lower bound $M$ on all divergent scalar coordinates such that
satisfying these requirements makes each output agree with $v$ through $h$.
The finite coordinates remain exactly $(\mathbf c,\mathbf f)$.

The joint support (FNS.26) supplies one tuple of feasible ranks at this same
$M$. At those ranks and finite profiles, use [SLP, Lemma 2.1 and Corollary
3.2][SLP] on every row's entire negative conjunction to prescribe its infinite
prefixes and reconstruct one finite residual tuple. Repeated names share
one filling; independent frontier holes are introduced only for distinct
names within that normalized chart. Lemma 4.2 then maps each tuple to an
actual original $u_r\in D_r$. All outputs agree with the single $v$ through
$h$, hence with one another through $h$. Every old positive identification,
exterior, negative, guard, sign, epoch and full target row holds on those
finite sources by the source correspondence, not by evaluation at $v$.
This proves $J_B(h)$ for every $h$.

If (FNS.27)'s right side is false, some finite $H$ has $\neg J_B(H)$ by the
necessity direction. This existence implication is not an effective test for
absence of unknown contacts. The same argument includes zero scalar or
residual dimensions, empty conjunctions and empty chart families. $\square$

**Theorem 5.3 (effective supplied-profile locus and finite reconstruction).**
For every supplied $(\mathbf b,\mathbf A,\mathbf F,\mathbf f)$,
(FNS.26) has a terminating exact Presburger description in all its finite
scalar parameters. The same holds for supplied finite templates
$\mathbf f(\mathbf c)$ by Corollary 2.6. If a common completed map (FNS.24)
is separately proved at the same finite point $\mathbf c$ with computable
finite prefixes, membership of that point in this locus produces actual
finite signed witnesses for each requested $h$. Recognizing a valid
common-map certificate does not show that all contacts have been
found. No decision over unknown $\mathbf f$ or arbitrary common maps follows.

**Proof.** Conjoin the fixed-profile support formulas (FNS.25) on their one
joint tuple and quantify the simultaneous lower bound as in (FNS.26).
Presburger quantifier elimination and witness extraction terminate. This is
the fixed-parameter cofinal step of [PAC, Theorem 4.2][PAC], following the
native support and lifting interfaces already in [SLP, Corollary 3.2][SLP].

For its semilinear form, decompose the joint support in
$\mathbb N^{\mathbf c}\times\mathbb N^{\mathbf w}$ into finitely many linear
sets. A component is eligible exactly when its periods with **zero finite
$\mathbf c$ part** collectively increase every required $\mathbf w$
coordinate. Summing those periods gives $(0,\mathbf q)$ and a cofinal ray
with that same fixed $\mathbf c$. In a fixed-$\mathbf c$ fiber, coefficients
of periods with a positive finite-parameter component are bounded. If a
component has no zero-$\mathbf c$ period increasing one required divergent
coordinate, that coordinate is bounded on this fiber. Finitely many such
ineligible components cannot meet all simultaneous lower bounds. The locus
is therefore exactly the projection of the eligible components. When there
are no divergent coordinates, every component is eligible and this is
ordinary support nonemptiness; zero finite-parameter dimensions are literal
empty vectors.

For reconstruction, compute the certified common prefix requirements,
extract one joint rank tuple from (FNS.26), and apply the finite simultaneous
SLP lifting in Theorem 5.2. A supplied functional graph as in Lemma 3.3 can
provide such prefixes, after exact positive source normalization and a proof
of its common-output equations. It is not assumed for every normalized
acquired input. Alternatively, each fixed $h$ is an exact finite native
query by [NSF, Theorem 5.2][NSF], so whenever (FNS.27) holds that query returns
finite source witnesses. If no contact exists, increasing finite-depth
queries eventually find an exclusion depth; if a contact exists, that NO
search does not terminate. No unconditional terminating alternative is
claimed for unknown contacts. $\square$

**Corollary 5.4 (full rows and the remaining contact problem).** Neither
cofinal arithmetic feasibility alone nor the simple switching equations
$Y_i=E_i$ alone decide (FNS.27). They do not impose a positive old-row
pullback omitted from the raw map. Lemma 4.2 keeps every old identification
by positive normalization; the resulting maps, not an assumed unchanged
raw parameterization, are the inputs to (FNS.24). Locating an unknown common
map with its arbitrary finite profile remains open. A finite exclusion for
one supplied $B$ does not settle other attained full rows in the same fiber.

## 6. A concrete consumer with no atomic-output anchor

Take $k=1,m=2$ and the seven-role context

$$
W(a,x,v,y,t,z,w)=
\langle a,\langle x,\langle v,\langle y,\langle t,\langle z,w\rangle\rangle\rangle\rangle\rangle.
\tag{FNS.28}
$$

Its role addresses in order are $L,RL,RRL,RRRL,RRRRL,RRRRRL,RRRRRR$.
Put

$$
F_n(t)=\langle\alpha,\langle T_n,\rho t\rangle\rangle,
\qquad
G(y)=\langle\beta,\rho y\rangle,
\tag{FNS.29}
$$

and

$$
U(n,x,v,y,t)=W(T_{n+2},x,v,y,t,F_n(t),G(y)).
\tag{FNS.30}
$$

Here $P=\{\varepsilon\}$ has its complete singleton root row, while
$Q$ is exactly the seven displayed role addresses with exterior $W$. Retain
all displayed branch and ground literals, the atomic record (FNS.18), and the links for the displayed $F_n$ and $G$
tokens, with both endpoint guards and their actual epochs. This is a paid
installation input, not a semantic declaration supplied for free.

For the displayed instance, with $p_a,p_t,p_z,p_y,p_w$ the role
representatives, the epoch-zero links and grounds are explicitly

$$
\begin{gathered}
r_{p_z}(L)=\alpha,\qquad r_{p_w}(L)=\beta,\\
(0,p_zRL,\ 0,p_aR,\ =),\qquad
(0,p_zRR,\ 1,p_t,\ =),\qquad
(0,p_wR,\ 1,p_y,\ =).
\end{gathered}
\tag{FNS.30a}
$$

For this displayed input the complete record list consists of these literals,
the branches of $W$ and the payload pairs, (FNS.18), and (FNS.30a), with
both reach guards and all repetitions. There are no additional off-task
records in this instance. The authentic final epoch satisfies $N\ge1$. If
further records are supplied, Lemma 4.2 retains all of them; the explicit seeds
below are not witnesses for an unchecked extension of this input.

Let $r_0$ have complete partition

$$
\pi_0=\{\{1\},\{2,4\},\{3,5\},\{6\},\{7\}\},
\tag{FNS.31}
$$

and $r_1$ have

$$
\pi_1=\{\{1\},\{2,6\},\{3,7\},\{4\},\{5\}\}.
\tag{FNS.32}
$$

Their exact strata are

$$
\begin{aligned}
\Theta_0(n,y,t)&=U(n,y,t,y,t),\\
\Theta_1(n,y,t)&=U(n,F_n(t),G(y),y,t),
\end{aligned}
\tag{FNS.33}
$$

with all cross-class target inequalities retained. The old root predicate
is automatic on every nonempty finite filling of $W$; it places no equality
on its different role slots. Thus (FNS.33) has both directions by Theorem
4.4 for this entire input. The common completed output equations are

$$
Y=F_c(T),\qquad T=G(Y),
\tag{FNS.34}
$$

after fixing the finite atomic coordinate $c$.

**Proposition 6.1 (actual finite witnesses after the common map).** Set
$y_0=\langle\alpha,\alpha\rangle$ and
$t_0=\langle\beta,\beta\rangle$, and recursively

$$
y_{q+1}=F_c(t_q),\qquad t_{q+1}=G(y_q).
\tag{FNS.35}
$$

For every requested depth $h$, choose $q=h+1$. Then

$$
u_{0,h}=W(T_{c+2},y_q,t_q,y_q,t_q,F_c(t_q),G(y_q)),
\tag{FNS.36}
$$

$$
u_{1,h}=W(T_{c+2},F_c(t_q),G(y_q),y_q,t_q,F_c(t_q),G(y_q))
\tag{FNS.37}
$$

are finite sources in $D_{r_0}$ and $D_{r_1}$ and satisfy
$u_{0,h}\equiv_hu_{1,h}$.

**Proof.** First prove the common completed map (FNS.34). The map
$(Y,T)\mapsto(F_c(T),G(Y))$ is guarded by its displayed pairs. Each
unfolding gains an original-prefix level, so the iterates have one unique
finite-prefix limit $(Y_\infty,T_\infty)$ satisfying (FNS.34). This is the
guarded-prefix argument of [FJC, Theorem 3.1], applied after the explicit
root links have been eliminated; bare $\rho$ is not treated as a contraction.

Next use constructor mass $\gamma$ from [URR, Definition 2.1]. The seeds
have mass one, and

$$
\gamma(F_c(t))=\gamma(t)+2,\qquad
\gamma(G(y))=\gamma(y)+1
\tag{FNS.38}
$$

whenever the displayed arguments have positive mass. If $a_q=\gamma(y_q)$
and $b_q=\gamma(t_q)$, then $a_0=b_0=1$,
$a_{q+1}=b_q+2$ and $b_{q+1}=a_q+1$. Induction gives
$a_{2r}=b_{2r}=1+3r$ and $(a_{2r+1},b_{2r+1})=(3+3r,2+3r)$. Thus
$a_q-b_q$ is zero or one, proving $y_q\ne F_c(t_q)$ and
$t_q\ne G(y_q)$. Their left children distinguish the remaining classes,
while the atomic $T_{c+2}$ has mass zero. Thus every inequality in
(FNS.31)--(FNS.32) holds, and the installation records hold by (FNS.29)--
(FNS.30).

Guarded unfolding gives $y_q\equiv_{q-1}y_{q+1}$ and
$t_q\equiv_{q-1}t_{q+1}$. Substituting (FNS.35) into the two outer contexts
therefore proves $u_{0,h}\equiv_hu_{1,h}$. These are actual finite source
witnesses obtained after the common completed map was proved. The completion
itself is not presented as an acquired row or a runtime value. $\square$

**Proposition 6.2 (the consumer is not an atomic-output anchor).** At fixed
$c$, the masses of the finite sources (FNS.36)--(FNS.37) are unbounded as
$q$ grows. Consequently no finite residual-free template family with a
uniform constructor-mass bound can cover this consumer's all-depth witnesses.

**Proof.** From (FNS.38), the two residual masses grow linearly with $q$ and
the outer context adds a fixed positive amount. Any finite residual-free
template made from fixed grounds, rank atoms and finitely many ordered pairs
has a fixed mass bound: rank atoms have mass zero and each displayed pair adds
at most one. A finite union has one common bound, whereas (FNS.36)--(FNS.37)
exceed it. This is a sourcewise finite obstruction to an atomic-output anchor,
not an undecidability or universal rank-free impossibility theorem. $\square$

The completed solution of (FNS.34) is itself non-finite. Along the repeated
right-pair path, its subtrees contain arbitrarily high atomic iterates
$T_{c+2q}$, so native atomic-rank injectivity makes the contact non-rational.
This observation explains why finite witnesses must be produced by guarded
prefix lifting rather than by declaring the limit a finite source.

## 7. Paid acquisition, service boundary and evidence ownership

The source maps, finite profiles, completions and SLP fillings above are
mathematical certificates. Under Assumption 1.3, the ARH producer obtains the
old complete row and every scheduled endpoint using paid original-root reads
before the authentic cut at $N$, compares both endpoints while accessible,
and retains the complete successful state. A forgotten traversal length or
cache is not silently free; complete accessible-state factoring must include
it in the premise. Conversely, the finite witnesses above do not select the
actual source, read an old version, reset or reroot the register, or inspect
an equality port.

For a target cut, a lawful observer still has only current-register
$\mathsf{Read}(p)$, serial forward $\mathsf{ApplyRho}$ and its counted local
state. A finite profile, a URR section, a completion prefix, an equality
partition in a proposed row, and a source chart are offline mathematical
objects. The full source correspondence and the conditional finite
reconstruction do not prove a uniform read, word, memory or physical
acquisition bound.

The source/repository ownership checked for the reused interfaces is:

| Owner | Reused scope and boundary |
| --- | --- |
| [ARH][ARH] | Definitions 1.1--1.2, Assumption 1.3, Proposition 2.1 and Application 26.1: complete acquired rows, guarded same-source records, paid producer and actual prefix interface. It does not decide arbitrary completed contact. |
| [ABC][ABC] | Theorems 2.2--2.3: native normal coding, smart pairing, rank injectivity and the interpreted shift. It does not turn $\rho$ into a free unary constructor. |
| [NIC][NIC] | Theorems 3.2--3.3 and 4.3: exact positive mixed images, complete signed pullback and both source inclusions for every retained old partition. A rank projection is not the whole image. |
| [NSF][NSF] | Lemma 5.1 and Theorem 5.2: exact fixed-navigation cases, full signed finite feasibility and witness reconstruction; these do not decide all-depth contact. |
| [NPL][NPL] | Theorem 5.3: exact finite whole-row image and original realizers. Example 9.4 and Open problem 10.1 prevent inferring a bounded full-row selector or unrestricted stopping from that list. |
| [URR][URR] | Definition 2.1, Theorem 3.1 and Corollary 3.2: one simultaneous finite residual witness and exact scalar support on a Cartesian carrier. It supplies no contact classifier. |
| [SLP][SLP] | Lemma 2.1, Theorem 3.1 and Corollary 3.2: support closure, arbitrary supplied-f support and simultaneous finite-prefix reconstruction after ranks and finite barriers are fixed. It does not choose unknown finite barriers or a common map. |
| [FJC][FJC] | Theorems 3.1, 5.1 and 7.1: guarded recursive contact, finite-prefix synthesis and the boundary of rank-free covers. Its rank-free result is not imported as a universal reduction. |
| [PAC][PAC] | Theorem 4.2: exact parametric cofinal semilinear loci and cofinal-ray extraction. Its finite-parameter hypotheses are rechecked here; it supplies no arbitrary feedback classifier. |
| Native observer sources | NativeCutFibers.rowFiberEquiv/legal_values_row, NativeHistoryCells.historyCellEquiv/cell_feasibility_exact, NativeDepthPatterns.original_prefix_locality/depthEquiv, and DelayedOriginalReadout.original_decoder_correct/original_decoder_service. The history-cell interface has literal epoch/address/reply histories; arbitrary signed records use the separate ARH/NIC bridge. No new compiled application is claimed. |

The supplied-f support compiler and finite-neighborhood reconstruction are
credited to SLP Corollary 3.2; fixed-parameter cofinal arithmetic is credited
to PAC Theorem 4.2. Sections 2 and 5 use their composition, including the
finite-template parameter extension. The repository-derived application is
the exact acquired joint-contact correspondence after full positive
normalization, together with the rank-parametric anchorless switching
consumer. No new separator, supplied-f solver or fixed-point theorem is
claimed. No literature-wide priority claim is attached to this composition.

**Definition 7.1 (primary literature and transfer limits).**

- Comon--Lescanne, *Equational Problems and Disunification*, JSC 7 (1989),
  §§3.2 and 6.2, supplies free-signature disunification background and
  explicitly limits transfer to general nontrivial equational theories. It
  does not supply the native $\rho$ rank argument or acquired-source rows.
- Milius--Moss, *The Category Theoretic Solution of Recursive Program
  Schemes*, arXiv:0904.2385v2, §7.3 and Theorem 7.15, supplies guarded
  recursive-scheme fixed-point background under its complete-metric and
  contracting hypotheses. Here the prefix gain is proved after root-link
  elimination; finite native trees are not assumed complete and bare $\rho$
  is not assumed contractive.
- Ginsburg--Spanier, *Semigroups, Presburger Formulas, and Languages*,
  Theorem 1.3, supplies the effective semilinear/Presburger correspondence
  used after exact native support reduction. Scalar Presburger decidability
  alone does not decide arbitrary tree feedback.

The pending NCC and NGE manuscripts are overlap markers only. The pending
FINITE_FRAME_MEMORY and SYMBOLIC_FEEDBACK_SYNTHESIS manuscripts are not
premises, and no producer correspondence, correctness or merge status is
inherited from them. The pinned [coupled-rank source][CRE] supplies a scoped
native obstruction and consumer boundary; it does not supply the unknown
completed-contact classifier.

## 8. Remaining obligations and explicit nonclaims

The exact source covers and (FNS.27) retain arbitrary complete acquired
signed-native inputs. What remains open is an effective complete search for
the common outputs and arbitrary finite profiles quantified there. Positive
normalization can reparameterize interacting residuals and produce
nonfunctional common-output equations, constructor/residual overlaps or
unknown finite barriers. The simple functional switching graph is not proved
to classify these normalized equations. Deciding every supplied profile or
recognizing a valid common-map certificate does not discharge that missing
classification, and no finite catalogue of profiles is substituted for it.

The result does not claim arbitrary completed-contact classification,
unrestricted $J_B$ stopping, physical certification of accessible-state
factoring, an optimal whole-image memory theorem, a universal observer
interface, undecidability, external novelty, spacetime recovery or completion
of the full programme. A finite exclusion for one $B$ does not settle other
rows. Finite-source signed records and row partitions remain finite facts;
limits supply only common-prefix equations. These boundaries are part of the
statement, not deferred validation.

## References

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md

[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md

[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md

[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md

[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md

[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md

[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md

[FJC]: RECURSIVE_RELATIONAL_OBSERVATION_FUNCTIONAL_JOINT_CONTACT.md

[PAC]: RECURSIVE_RELATIONAL_OBSERVATION_PARAMETRIC_ATOMIC_CONTACT.md

[CRE]: RECURSIVE_RELATIONAL_OBSERVATION_COUPLED_RANK_ESCAPE.md

## 追加锚（本行以下为增补区）
