# Finite-native cofinal spectra for source-faithful joint prefixes

> This generic-v1 volume is ordinary mathematical reference input. It uses the
> supplier material at revision '5c920a039f074b6274e8a033ea9c99b556e4c86a' as
> fallible repository evidence. No Lean, Blueprint, registry, compilation or
> frozen-status claim is made here. The construction below is a scoped result
> for a recognized finite installation schema; it does not close the arbitrary
> completed-contact problem.

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
chart supplies a finite native source map

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
unique empty finite profile. These conventions include all zero-dimensional
edges.

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

**Proof.** Instantiate [NIC, Theorems 3.2--3.3][NIC] on the chart's positive
source map and the complete list (FNS.9). The two source inclusions are
essential: every satisfying parameter assignment reconstructs the same
original source, and every original source supplies its own parameters.
For the fixed finite tuple $\mathbf f$, expand its finite syntax as ground
native trees. The resulting negative list is in the mixed grammar of [URR,
Definition 1.2][URR], with scalar variables $(\mathbf c,\mathbf w)$ and
Cartesian residual variables $\mathbf z$.

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
single simultaneous rank tuple. The URR section (FNS.13), followed by the
NIC inverse source map, supplies one finite residual tuple satisfying all
whole disequalities together. Substitution into (FNS.8) preserves every
shared occurrence and every original signed guard. The converse is projection
of any finite source witness. Negating (FNS.11) gives the finite bound in the
second statement. No uniform source-size, source-depth or read-cost bound
follows. $\square$

**Corollary 2.5 (joint support is not a marginal support).** Replacing
(FNS.11) by separate assertions $\forall M\exists w_j\ge M$ for each
coordinate can change its truth value. A valid spectrum retains the one
conjunction $P_b\land\Delta_b$ and one tuple $\mathbf w$ satisfying every
coordinate lower bound at once. Likewise, replacing $\Delta_b$ by one
selected residual witness per inequality can change feasibility when residual
names are shared.

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
whole signed inequalities remain in the chart predicates.

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

1. a finite mode $A$ identifying the scalar coordinates that diverge, with a
   fixed finite complement $\mathbf c$;
2. a proved completion map for every row piece, preserving finite-prefix
   locality and the same shared residual names; and
3. a proof that the completed outputs of all rows in $B$ agree for one common
   completed residual tuple, with the same finite profile before all depths.

This certificate is a mathematical bridge. It is not a source-selection or
runtime equality port.

**Lemma 3.3 (finite-coordinate graph lemma for the recognized map).** Consider
the finite feedback equations obtained from a recognized switching map after
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
cycle is a free state; assign it the all-branch representative. This choice
does not invent a residual solution: after the finite negative list is
inserted, URR equality reflection supplies one common finite residual witness
whenever any witness exists.

For acyclic root links, substitute along the unique finite path, accumulating
the weight. What remains is a finite system in which every recursive
occurrence is below a pair. Simultaneous unfolding gains one original-prefix
level at each such pair. The finite-prefix contraction argument of [FJC,
Theorems 3.1 and 5.1][FJC] therefore gives one completion for each free
state. Reverse topological evaluation identifies exactly the coordinates
whose values are finite mixed templates in $\mathbf c$; these are $F_A$ and
$f_i^A(\mathbf c)$. A cycle containing a pair cannot be finite because a
finite leaf would have to occur strictly below itself after one or more
guarded unfoldings. Native $\rho$ never removes a leaf.

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

## 4. A recognized acquired switching family

The next definitions give one faithful consumer of the preceding interface.
They are deliberately source-installation data, not a claim that every
acquired input has this form.

**Definition 4.1 (installation schema).** Choose integers $k\ge1$ and
$m\ge2$, a finite ordered context $C$, and distinct prefix-free original
addresses for roles

$$
A_1,\ldots,A_k,\quad X_i,Y_i,Z_i\ (1\le i\le m).
\tag{FNS.17}
$$

The old row contains the complete concrete exterior and the full role
partition. At $A_j$ retain a branch literal and the guarded record

$$
(1,p_{A_j}L,\ 0,p_{A_j},\ =).
\tag{FNS.18}
$$

Each payload template $E_i(\mathbf n,\mathbf y)$ is built from finite
grounds, $T_{n_j+d}$, fixed $\rho$ powers of $Y$ roles and ordered pairing.
Install every displayed pair and ground by actual literals. A residual token
$\rho^a(Y_\ell)$ is linked by the guarded record

$$
(0,p_{Z_i}q,\ a,p_{Y_\ell},\ =),
\tag{FNS.19}
$$

and an atomic token $T_{n_j+d}$ is linked to the corresponding right child of
$A_j$ at epoch $d$. Structural navigation stops at an unknown token and never
descends into it. Add any finite rank-only guarded records and any finite list
of structural whole disequalities at their actual epochs. Let $K(\mathbf n)$
be the exact Presburger condition for all residual-free records.

The recognizer requires that these lists, all repetitions, all endpoint
guards and the complete old row are the entire retained input for this
schema. A failed recognition is outside the theorem; it is not a NO answer
for arbitrary acquired inputs.

**Lemma 4.2 (source map and entire fiber).** Put

$$
U(\mathbf n,\mathbf x,\mathbf y)
  =C\big[A_j:=T_{n_j+2},\ X_i:=x_i,\ Y_i=y_i,\ Z_i:=E_i(\mathbf n,\mathbf y)\big].
\tag{FNS.20}
$$

After translating every retained structural negative, let
$\Delta(\mathbf n,\mathbf x,\mathbf y)$ be the full conjunction of those
negatives and every distinct-role inequality of the complete old row. Then

$$
D=\{U(\mathbf n,\mathbf x,\mathbf y):
\mathbf n\in\mathbb N^k,\ K(\mathbf n),\ \mathbf x,\mathbf y\in\mathcal T^m,
\ \Delta(\mathbf n,\mathbf x,\mathbf y)\}.
\tag{FNS.21}
$$

**Proof.** At an atomic role, (FNS.18) says that if
$A_j=\langle s,t\rangle$ then $\rho s=\langle s,t\rangle$. The finite
feedback classification in [ARH, Application 26.1][ARH] gives the unique
finite solution $(s,t)=(T_{n_j+1},T_{n_j})$, so $A_j=T_{n_j+2}$. Induction over
the displayed payload syntax, using (FNS.19), gives exactly $E_i$ on the same
original $Y$ values. The rank-only records are exactly $K$; every structural
endpoint remains reached at its recorded epoch, so each signed comparison is
the stated whole mixed comparison.

Conversely, evaluate (FNS.20) on any finite tuple satisfying the right side
of (FNS.21). The atomic recurrence
$T_{n+2}=\langle T_{n+1},T_n\rangle$ proves every guarded installation
record. The displayed pair and ground literals and every link hold by
induction. $K$ proves all residual-free records, and $\Delta$ restores every
old inequality and signed record. The exterior and all repeated role values
are exactly those of the old row. The two directions reconstruct the same
original source; they do not merely produce an observationally equivalent
parameter tuple. $\square$

**Definition 4.3 (complete row strata).** For each
$\sigma\in\{0,1\}^m$, let $r_\sigma$ have the common exterior and all role
holes reached. In row $r_\sigma$, set

$$
X_i=\begin{cases}
Y_i,&\sigma_i=0,\\
Z_i,&\sigma_i=1,
\end{cases}
\tag{FNS.22}
$$

and put all other role pairs in distinct equality classes. Let
$\Theta_\sigma(\mathbf n,\mathbf y)$ be (FNS.20) after the simultaneous
substitution (FNS.22), and let $\Delta_\sigma$ include every full partition
inequality, every off-task condition and every translated signed record.

**Theorem 4.4 (exact strata in both directions).**

$$
D_{r_\sigma}=\{\Theta_\sigma(\mathbf n,\mathbf y):
K(\mathbf n)\land\Delta_\sigma(\mathbf n,\mathbf y)\}.
\tag{FNS.23}
$$

Each occurrence of a shared $Y_i$ or $n_j$ is the same coordinate throughout
the complete conjunction. Row labels are complete original rows, not selected
output bits.

**Proof.** Substitution makes every within-class equality literal. The full
$\Delta_\sigma$ makes every distinct-class inequality and every signed record
hold on one source. Conversely, an original source with row $r_\sigma$ forces
exactly the equalities in (FNS.22), so its role values reconstruct as
$\Theta_\sigma$ and its complete predicates become $K\land\Delta_\sigma$.
This uses (FNS.21) and therefore retains the same original source in both
directions. Feasibility of a row is checked by the existing finite native
feasibility result; no row is declared attained from a selected witness bit.
$\square$

## 5. The joint finite-profile spectrum and the stopping alternative

Let $B$ be any finite set of at least two distinct attained rows among the
$r_\sigma$. Let $V$ be the set of coordinates at which $B$ contains both
values of $\sigma_i$. Equality of completed outputs for rows in $B$ imposes
the partial feedback equations

$$
Y_i=E_i(\mathbf n,\mathbf Y)\qquad(i\in V).
\tag{FNS.24}
$$

Coordinates outside $V$ already have the same $X_i$ placement in every row
and impose no new equation. The equations (FNS.24) are derived from the
source map and complete rows; they are not imported as a supplied completion
presentation.

**Definition 5.1 (mode and arbitrary finite-profile locus).** A mode
$A\subseteq\{1,\ldots,k\}$ declares the atomic coordinates $n_j$ with
$j\in A$ divergent and the others equal to one common finite vector
$\mathbf c$. Apply Lemma 3.3 to (FNS.24). It gives a forced finite set
$F_A$ and templates $f_i^A(\mathbf c)$ for $i\in F_A$. For each row
$\sigma\in B$, write $\mathbf w_\sigma$ for its remaining divergent rank
coordinates and define

$$
\Psi_{\sigma,A}(\mathbf c,\mathbf w_\sigma)
\Longleftrightarrow
K(\mathbf c,\mathbf w_\sigma)\land
\exists\mathbf z_\sigma\;
\Delta_\sigma(\mathbf c,\mathbf w_\sigma,
               \mathbf f^A(\mathbf c),\mathbf z_\sigma),
\tag{FNS.25}
$$

where the finite coordinates are inserted into the entire original
conjunction and every remaining residual is left Cartesian. By Theorem 2.3,
the existential residual part in (FNS.25) has an exact Presburger compiler.

The joint cofinal locus is

$$
\mathcal G_A=\left\{\mathbf c:
\forall M\;\exists(\mathbf w_\sigma)_{\sigma\in B}
\left[
\bigwedge_{\sigma\in B}\Psi_{\sigma,A}(\mathbf c,\mathbf w_\sigma)
\land
\bigwedge_{\sigma\in B}\bigwedge_{j\in A}w_{\sigma,j}\ge M
\right]\right\}.
\tag{FNS.26}
$$

The same finite $\mathbf c$ and the same finite native templates
$\mathbf f^A(\mathbf c)$ occur for every row and every requested depth. The
rank tuple $\mathbf w_\sigma$ may differ between alternative rows; forcing
those tuples to equal would change the source problem.

**Theorem 5.2 (recognized joint-prefix alternative).** For the recognized
installation schema and finite attained $B$,

$$
\forall h\in\mathbb N\;J_B(h)
\quad\Longleftrightarrow\quad
\exists A\subseteq\{1,\ldots,k\}\;\mathcal G_A\ne\varnothing.
\tag{FNS.27}
$$

If the right side holds, every requested $h$ has effectively constructible
finite sources in every row sharing one original prefix through $h$. If every
$\mathcal G_A$ is empty, a finite exclusion depth $H$ exists with
$\neg J_B(H)$. The result is scoped to the recognized family and does not
classify arbitrary nonfunctional completed equations.

**Proof (sufficiency).** Choose $A$ and $\mathbf c\in\mathcal G_A$. The
Presburger formula (FNS.26) supplies, for any lower bound $M$, one rank tuple
for every $\sigma$ satisfying all signed predicates jointly. Choose $M$ above
the finite-prefix threshold for depth $h$; atomic $T_{w_{\sigma,j}}$ then
agrees with $\Omega$ through the requested prefix. Insert the common finite
templates $f_i^A(\mathbf c)$. For each row, Theorem 2.3 supplies a finite seed
for the whole negative conjunction, not separate seeds for its clauses.

The remaining canonical residual coordinates have infinite frontiers. Apply
[SLP, Lemma 2.1][SLP] to prescribe the one common completed-map prefix on
each repeated residual name and to satisfy all signed disequalities
simultaneously. Repeated names retain one shared filling. Evaluate
$\Theta_\sigma$. Native $\rho$ is prefix nonexpanding and every explicit pair
adds one address level, so equal completed prefixes yield
$\Theta_\sigma\equiv_h\Theta_\tau$ for all rows. The exact stratum theorem
(FNS.23) supplies actual finite sources with their original complete rows.
No finite row sign or partition has been assigned to the completion point.

**Proof (necessity).** Assume $J_B(h)$ for every $h$ and choose one finite
witness tuple at each depth. There are finitely many row-piece choices and
finitely many modes for the atomic rank coordinates. A diagonal subsequence
of finite native trees has a common finite-prefix limit in the completed tree
space. Atomic ranks either stabilize at a finite value or diverge; pass to one
mode $A$. A stabilized atomic tree is isolated, hence its eventual value is
one common finite $c_j$. The completed equalities of the varying row labels
give (FNS.24). Lemma 3.3 forces each finite graph coordinate to be the same
template $f_i^A(\mathbf c)$; a free infinite coordinate is retained as a
frontier coordinate rather than silently fixed to a finite marker.

For any $M$, take the subsequence beyond the point where every divergent rank
is at least $M$ and every forced finite coordinate has its stabilized value.
Project the witnesses through the exact stratum maps (FNS.23). Their residual
values satisfy the complete predicates, so the definition of
$\Psi_{\sigma,A}$ gives one tuple in (FNS.26). This proves
$\mathbf c\in\mathcal G_A$.

The diagonal argument uses only finite-prefix locality and the finite graph
certificate. It does not assert that a completion point is a finite source,
that its signed predicates are defined, or that a general acquired input has
such a graph. $\square$

**Theorem 5.3 (termination and finite exclusion).** The test in (FNS.27)
terminates for the recognized family. Each $\mathcal G_A$ has an effective
Presburger description. If some locus is nonempty, rank witnesses and the
finite-prefix construction in Theorem 5.2 terminate for each $h$. If all
loci are empty, sequential finite-depth feasibility tests terminate at the
first failed depth and return a finite $H$.

**Proof.** There are finitely many modes. The graph and finite-template
construction terminates. For each $A$ and $\sigma$, Theorem 2.3 gives a
Presburger formula for (FNS.25), and (FNS.26) is its finite-dimensional
Presburger quantifier formula. Quantifier elimination decides emptiness and
extracts $\mathbf c$. Equivalently, a semilinear decomposition has a component
whose periods jointly increase all coordinates in $A$; summing those periods
gives a cofinal ray with fixed $\mathbf c$. A component that fails to increase
one required coordinate cannot meet all simultaneous lower bounds.

In the nonempty case, Presburger extraction, finite canonical-prefix
evaluation and SLP's finite simultaneous lifting all terminate. In the empty
case, Theorem 5.2's necessity proves that not all $J_B(h)$ hold. Each fixed
$h$ is a finite native feasibility query covered by [NSF, Theorem 5.2][NSF],
so increasing $h$ eventually reaches a false query. This is a terminating
mathematical procedure, not an experimental search and not a claim of a
uniform resource bound. $\square$

**Corollary 5.4 (scope of a NO).** The finite depth returned by Theorem 5.3
excludes only the supplied complete-row set $B$. Other attained rows in the
same acquired fiber require their own joint test. A maximum of pairwise
exclusion depths becomes a whole-fiber stopping certificate only after every
required distinct row set has been handled.

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

Retain the complete root old row, all displayed branch and ground literals,
the atomic record (FNS.18), and the links for the displayed $F_n$ and $G$
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

The records in (FNS.30a) include both reach guards; all repeated occurrences
and every other old or off-task record are retained in the complete input.
The authentic final epoch satisfies $N\ge1$ (and any later scheduled epoch).

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

with the entire old partition, all cross-class inequalities and all signed
records retained. The common completed output equations are

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

whenever the displayed arguments have positive mass. Hence $y_q\ne F_c(t_q)$
and $t_q\ne G(y_q)$; their left children also distinguish the remaining
classes, while the atomic $T_{c+2}$ has mass zero. Thus every inequality in
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
objects. The theorem proves sourcewise existence in the recognized family;
it does not prove a uniform read, word, memory or physical acquisition bound.

The source/repository ownership checked for the reused interfaces is:

| Owner | Reused scope and boundary |
| --- | --- |
| [ARH][ARH] | Definitions 1.1--1.2, Assumption 1.3, Proposition 2.1 and Application 26.1: complete acquired rows, guarded same-source records, paid producer and actual prefix interface. It does not decide arbitrary completed contact. |
| [ABC][ABC] | Theorems 2.2--2.3: native normal coding, smart pairing, rank injectivity and the interpreted shift. It does not turn $\rho$ into a free unary constructor. |
| [NIC][NIC] | Theorems 3.2--3.3 and 4.3: exact mixed images, complete signed pullback and both source inclusions. A rank projection is not the whole image. |
| [URR][URR] | Definition 2.1, Theorem 3.1 and Corollary 3.2: one simultaneous finite residual witness and exact scalar support on a Cartesian carrier. It supplies no contact classifier. |
| [SLP][SLP] | Lemma 2.1 and Theorem 3.1: simultaneous signed prefix lifting after ranks and finite barriers have been fixed. It does not choose an unknown completed map. |
| [FJC][FJC] | Theorems 3.1, 5.1 and 7.1: guarded recursive contact, finite-prefix synthesis and the boundary of rank-free covers. Its rank-free result is not imported as a universal reduction. |
| [PAC][PAC] | Theorem 4.2: exact parametric cofinal semilinear loci and cofinal-ray extraction. Its finite-parameter hypotheses are rechecked here; it supplies no arbitrary feedback classifier. |
| Native observer sources | NativeCutFibers.rowFiberEquiv/legal_values_row, NativeHistoryCells.historyCellEquiv/cell_feasibility_exact, NativeDepthPatterns.original_prefix_locality/depthEquiv, and DelayedOriginalReadout.original_decoder_correct/original_decoder_service. These are source and readout interfaces; no new compiled application is claimed. |

The exact finite-profile step is the repository-derived increment here. It
uses existing normalization, signed lifting and cofinal arithmetic while
retaining the arbitrary finite original tuple $\mathbf f$.

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
inherited from them. The coupled-rank source supplies a scoped native
obstruction and consumer boundary; it does not supply the arbitrary theorem
claimed here.

## 8. Remaining obligations and explicit nonclaims

The recognized family leaves the following relation open: arbitrary complete
acquired signed-native inputs may contain competing nonfunctional feedback,
residual-versus-constructor overlaps, image or inverse restrictions, and
unknown finite residual barriers that do not arise from the installation
schema. No reduction of every such input to (FNS.24)--(FNS.26) is proved.

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

[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md

[FJC]: RECURSIVE_RELATIONAL_OBSERVATION_FUNCTIONAL_JOINT_CONTACT.md

[PAC]: RECURSIVE_RELATIONAL_OBSERVATION_PARAMETRIC_ATOMIC_CONTACT.md

## 追加锚（本行以下为增补区）

