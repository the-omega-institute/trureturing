# Native minimum leaf depth and exact constructor-context contact

## 1. Finite sources, designated outputs and the acquired task

**Definition 1.1 (native syntax and minimum leaf depth).** Let

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&
\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle u,v\rangle&=\langle\rho u,\rho v\rangle.
\end{aligned}
\tag{NLC.1}
$$

Every member of $\mathcal T$ is nonempty, finite, ordered and free as a
binary tree. Powers of $\rho$ in a native expression have fixed natural
exponents. The expression grammar otherwise uses variables, the two
constants and pairing. In particular $\rho$ is interpreted by (NLC.1),
not treated as a free unary constructor. Put

$$
\begin{aligned}
\mu(\alpha)&=\mu(\beta)=0,\\
\mu(\langle u,v\rangle)&=1+\min(\mu(u),\mu(v)).
\end{aligned}
\tag{NLC.2}
$$

Thus $\mu(u)$ is the minimum original-root address length of a leaf.
For every natural $h$, $\mu(u)>h$ means that every address of length at
most $h$ is reached and has reply $\mathsf{branch}$. The equivalence
follows by following a shortest leaf path in one direction and by
induction through the binary levels in the other. This statistic is
neither maximum depth nor source size.

Let $\Phi(\mathbf x)$ be any finite quantifier-free Boolean combination
of native equalities, with all its variables ranging over $\mathcal T$.
Let $\mathbf t=(t_1,\ldots,t_s)$ be a nonempty finite tuple of native
expressions in those variables. Variables absent from the output tuple
are still jointly constrained by $\Phi$. Define

$$
\begin{aligned}
\operatorname{Sol}(\Phi)&=\{\mathbf x:\Phi(\mathbf x)\},\\
 m_{\mathbf t}(\mathbf x)&=\min_{1\le i\le s}\mu(t_i(\mathbf x)).
\end{aligned}
\tag{NLC.3}
$$

Fixed finite tree parameters are expanded as native expressions. Fixed
literal observations, guarded whole-subtree comparisons and exact row
tests are admitted through the exact compiler of [NSF, Lemma 5.1][NSF].
A designated reached-subtree expression has its reach guard imposed;
an absent endpoint is not assigned a fictitious tree. The compiler's
finite cases retain both reconstruction directions. No variable epoch,
variable physical word or universal pointwise predicate is added to this
quantifier-free language.

**Assumption 1.2 (entire acquired input and complete handoff).** For service
applications use exactly [ARH, Assumption 1.3][ARH]. Finite prefix-free
original cuts $P,Q$, the full old row $R$, finite literal history $H_0$
and finite signed guarded history $H_{\rm rel}$ determine

$$
D=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\}.
\tag{NLC.4}
$$

A signed record $(a,p,b,q,\bowtie)$ compares the entire subtrees
$(\rho^a u)|_p$ and $(\rho^b u)|_q$ and requires both endpoints reached,
for either $\bowtie={=}$ or $\bowtie={\ne}$. Every constraint is imposed
on the same original $u$. All repeated old classes, all cross-class and
off-task disequalities, the old concrete exterior, old absent-address
conditions and every additional record remain. The service premise is
$D\ne\varnothing$; consistency tests may also return an empty set.

The records were actually acquired before the cut. The one physical
original-root register is at $\rho^N u$, with authentic $N$ at least
all acquired epochs. The entire accessible state is a fixed recoverable
encoding of the retained input and common parameters. Every accessible
source-bearing cache, address, length, count, program position, timing
field, reference, permission, output and archive belongs to that state.
No unlisted field selects a smaller source fiber. These are handoff
premises, not consequences of a logical description of $D$. Pre-cut
acquisition may terminate sourcewise without a uniform sourcewise cost
bound.

The target is the full original row $R_Q(u)$: reached original holes in
their fixed order, numbered-hole concrete exterior and the complete
whole-subtree equality partition. A row label below always includes all
three fields. A limit object's recomputed partition never replaces a
finite source's label.

**Definition 1.3 (legal competitors and separate costs).** A competitor
is any deterministic effective post-cut controller that is correct and
terminates on every original $u\in D$. Its actual source operations are
original-root $\mathsf{Read}(p)$ at any finite physical word, forward
same-register $\mathsf{ApplyRho}$, and absorbing $\mathsf{Halt}$.
Replies are $\alpha,\beta,\mathsf{branch},\mathsf{absent}$ and may
control future operations. There is no reset, reroot, clone, equality,
source identity, chart-membership or unknown-source port. Computation
and updates convey no additional source information.

For such a controller $A$ keep the three different objects

$$
\begin{aligned}
c_A(u)&=(q_A(u),a_A(u),\ell_A(u)),
&\ell_A(u)&=\sum_{\text{actual reads at }p}|p|,\\
b(A)&=(\sup_D q_A,\sup_D a_A,\sup_D\ell_A),\\
W_\lambda(A)&=\sup_{u\in D}\lambda\cdot c_A(u),
&\lambda&\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{NLC.5}
$$

Every raw Read call counts, including repeated and absent reads; $a$
counts actual post-entry updates. A root read costs one call and zero
literal length. A same-source weighted sum is taken before its
supremum. Installation, computation, address generation, memory,
authentication, retention, acquisition and physical time are separate
costs. No hypothetical source or simulated operation produces an actual
receipt.

**Convention 1.4 (falsifiers and mathematical scope).** Omitting an
original solution, accepting an absent signed endpoint, or failing to
lift a constructed assignment to all retained constraints falsifies
source fidelity. Giving the same accessible observations different
claimed outputs falsifies behavioral sufficiency. An unpaid equality
test, hidden selector, backward action or simulated receipt falsifies
operation legality. Omitting a legal adaptive controller falsifies the
universal obstruction. Increasing a cost on one same source falsifies
a claimed sourcewise dominance; summing coordinate suprema changes the
weighted task. Replacing a finite rejection argument by an unbounded
unsuccessful search falsifies termination.

Theorems below give ordinary mathematical proofs, conditional on their
named ordinary suppliers and, for service assertions, Assumption 1.2.
They do not assert new Lean verification, physical realization, a
complexity bound or a solver implementation. Their new inference is an
exhaustive all-depth alternative for (NLC.3) and its exact supplied-context
consumer. General bounded full-row recovery remains the separate problem
in §9.

## 2. Reused normal branches and the all-solution direction

**Definition 2.1 (normal codes and effective branch data).** Reuse the
native normal-code bijection $B:\mathcal T\to\mathcal N$ and its inverse
$E$ from [ABC, Theorems 2.2–2.3][ABC]. A primitive $[r]$ expands to
$T_r=\rho^r\alpha$. A constructor code $F(X,Y)$ is normal exactly when
its children are normal and are not $[r+1],[r]$ for any $r\ge0$.
Native pairing uses the smart constructor that collapses exactly that
exceptional pair to $[r+2]$. Native $\rho^k$ adds $k$ to every primitive
rank and preserves the constructor nodes of a normal code.

Apply [NSF, §§2–4][NSF] to $\Phi$, after naming each designated output
and imposing its positive defining equation. Naming is a definitional
extension: evaluating an original assignment supplies the names, and
forgetting them recovers that same assignment. No output value is fixed
by the act of naming it.

The effective finite branch list includes Boolean and smart-constructor
cases, finite-tree shape unification with its occurs check, and the
negative disjunct choices for identical-shape disequalities. On a
successful shape branch each name has a finite shape term over primitive
shape $c$, constructor shape $f$, and residual shape variables
$w_1,\ldots,w_m$. Each explicit $c$ occurrence has a scalar rank. Each
$w_j$ occurrence has a rank-function block on that common, as yet
unspecified, nonempty finite shape. Repeated uses of a name reuse its
whole decorated template; two occurrences of a residual shape need not
have the same rank function.

The remaining positive comparisons have only the forms

$$
r=r'+d,\qquad r=d,\qquad U=V+d,
\qquad d\in\mathbb Z.
\tag{NLC.6}
$$

The third comparison is of whole blocks of the same residual sort,
with pointwise offset. There is no scalar/block comparison and no
comparison between blocks of different residual sorts. Scalar ranks
are natural. Explicit primitive cherries impose the scalar disequation
$r_L\ne r_R+1$. Negative branches also retain scalar and whole-block
offset disequations. A disequality between syntactically different
shape terms is retained as a disequality of the original decorated
codes: actual substitutions making their ground shapes equal are not
excluded merely by a syntactic test.

Add a scalar vertex $o=0$ and write every constant equation as an edge
to $o$. Consistent component potentials give

$$
r=b_C+\delta_r.
\tag{NLC.7}
$$

The component containing $o$ is anchored, and all its scalar ranks have
fixed computable values. Every other scalar component is free. The
block equation graphs have potentials separately for each residual
sort. They have no anchored vertex. These are exactly the data of
[NPL, Definitions 2.1–2.2][NPL].

**Lemma 2.2 (the two distinct supplier guarantees).** The finite branch
list has the following properties.

1. Every original solution extends to at least one branch and factors
   through its shape unifier. Its actual scalar ranks and actual block
   functions satisfy that branch's equations, selected negative
   conditions and normality of every full named code.
2. Each branch's feasibility is effectively decidable. For a feasible
   branch, NSF supplies a scalar solution and a witness assignment in
   which each residual sort is a fixed nonleaf shape marker and every
   block is constant on its marker's leaves. These witnesses expand to
   complete original assignments satisfying all constraints.

The second guarantee does not parametrize the assignments in the first.

Proof. These are [NSF, Lemmas 2.3, 3.2, 4.1–4.2 and Theorem 4.3][NSF],
with the distinction made explicit in [NPL, Lemma 2.3][NPL]. For the
first direction, evaluate all names in the actual source, choose the
actual collapse cases, factor its ground shapes through the most
general unifier, and choose a genuinely differing scalar or block in
each identical-shape disequality. A syntactically different-shape
negative is still its original negative, whether its actual ground
shapes coincide or not. Normality is the normality of the actual codes.

For the witness direction, nonzero offset cycles, impossible forced
ranks and forced-equal negative comparisons are rejected. All other
base constraints have lower bounds and finitely many forbidden
differences. NSF's finite potential procedure chooses bases. Its
pairwise distinct equal-mass nonleaf shape markers separate every
listed syntactic shape inequality. Constant ranks make internal marker
cherries normal; nonleaf roots prevent new primitive cherries at
insertion boundaries; explicit cherry inequalities handle the rest.
The equations then reassemble every named native expression and every
sign. These are the supplied witness conditions used below. $\square$

## 3. Physical leaf depth in normal coordinates

**Lemma 3.1 (rank-to-depth identity).** For all $r\in\mathbb N$,

$$
\mu(T_r)=\left\lfloor\frac r2\right\rfloor.
\tag{NLC.8}
$$

If a normal code $X$ has primitive rank $r_p$ at each code-leaf address
$p$, then

$$
\mu(E(X))=
 \min_{p\text{ a code leaf}}\left(|p|+\left\lfloor\frac{r_p}{2}\right\rfloor\right).
\tag{NLC.9}
$$

In particular an explicit primitive occurrence at code address $p$ and
rank $r$ supplies an actual native leaf at depth
$|p|+\lfloor r/2\rfloor$, regardless of all other code subtrees.

Proof. The cases $r=0,1$ are the two native leaves. The native recurrence
$T_{r+2}=\langle T_{r+1},T_r\rangle$, supplied by (NLC.1) and ABC,
gives

$$
\mu(T_{r+2})
 =1+\min\left(\left\lfloor\frac{r+1}{2}\right\rfloor,
                \left\lfloor\frac r2\right\rfloor\right)
 =\left\lfloor\frac{r+2}{2}\right\rfloor.
$$

This proves (NLC.8) by induction. Expansion preserves every displayed
$F$ as a native pair. Induction on the code therefore adds one to the
minimum at each such constructor, proving (NLC.9). To obtain the stated
leaf, follow $p$ and then a shortest leaf path in its finite $T_r$.
Neither formula identifies code leaves with native leaves. $\square$

**Definition 3.2 (output anchor set).** On a feasible branch $b$, let
$A_b$ be the finite set of explicit primitive occurrences in all the
designated output templates whose scalar belongs to the anchored
component. For an occurrence $e\in A_b$, let $p_e$ be its address
within its output code and let $r_e$ be its forced natural rank. If
$A_b\ne\varnothing$, put

$$
C_b=\min_{e\in A_b}
 \left(|p_e|+\left\lfloor\frac{r_e}{2}\right\rfloor\right).
\tag{NLC.10}
$$

These occurrences and their ranks are effective finite branch data.
The absence of an anchor elsewhere is not required. In particular
names used only by the constraints can have fixed primitive ranks.

**Lemma 3.3 (anchored bound on every original solution).** If
$A_b\ne\varnothing$, every original solution choosing branch $b$
satisfies $m_{\mathbf t}(\mathbf x)\le C_b$.

Proof. Use the first direction of Lemma 2.2, before making any marker
replacement. For every $e\in A_b$ the original output code has that
explicit primitive at the same displayed constructor address $p_e$.
The scalar equation path to $o=0$ forces its value to be $r_e$ on this
original solution. Arbitrary actual residual shapes and decorations do
not alter this occurrence. Lemma 3.1 supplies a native leaf at the depth
in (NLC.10) in that output. Taking the minimum over all outputs and all
such occurrences proves the bound. It does not bound each output, the
maximum depth of any output, or any source's size. $\square$

**Lemma 3.4 (simultaneous free-rank ray).** For every feasible branch
there are fixed shape markers, effectively chosen initial scalar and
constant-block ranks, and a computable $k_0\ge0$ with the following
property. For every integer $k\ge k_0$, retain every anchored scalar
rank, add $k$ to every free scalar rank and add $k$ to every
constant-block rank. This gives a complete original solution of that
same branch. All free scalar and block leaf ranks in it are at least
$k$.

Proof. Choose NSF's witness of Lemma 2.2, retaining its scalar ranks,
constant block ranks and nonleaf shape markers. These initial ranks
are all natural. Every scalar equation joins ranks in the same
component, so both its sides are shifted together or neither is.
Constant equations lie in the anchored component and stay true. Every
whole-block equation has both sides shifted by $k$, so also stays true.
Nonnegativity is preserved.

Consider scalar disequations, including explicit cherry normality.
When both ranks are free or both anchored, their difference is
unchanged. When one rank is free and the other anchored, failure can
occur at at most one integer $k$. The offending value is obtained by
solving that one offset equality using the initial ranks. Choose $k_0$
strictly larger than every nonnegative offending value, taking $k_0=0$
if there are none. The list is finite and effectively computable. All
scalar disequations then hold for every $k\ge k_0$.

Every block leaf rank is shifted, regardless of its block component,
so every selected whole-block offset disequation is unchanged. There
are no scalar/block or cross-sort positive or negative offset tests in
these identical-shape disjuncts. Syntactically different-shape negatives
are preserved by the unchanged separating markers.

Inside each inserted marker all leaf ranks remain equal. No cherry
there can have left rank one more than right rank. Its root is still
nonleaf, so no primitive cherry crosses an insertion boundary. All
remaining cherries are the explicit scalar cherries already checked.
Thus every whole named code is normal for every $k\ge k_0$.

The equations, negative witnesses and normality reassemble every
native subexpression as in Lemma 2.2. Expansion yields all original
variable values jointly. Each initial free scalar or block rank was
nonnegative, so its shifted value is at least $k$. The entire
construction is finite for each $k$ and does not evaluate an unknown
actual source. $\square$

The common shift in Lemma 3.4 is essential to its stated simultaneous
claim: pumping one output while leaving another anchored would not
make (NLC.3) unbounded. The witness ray is not an assertion that all
solutions have fixed residual shapes or constant block ranks.

## 4. A terminating all-depth alternative

**Theorem 4.1 (native simultaneous minimum-depth decision).** Given
$(\Phi,\mathbf t)$ of Definition 1.1, an effective terminating procedure
returns exactly one of the following three kinds of result.

1. **EMPTY:** $\operatorname{Sol}(\Phi)=\varnothing$.
2. **DEEP:** for every natural $h$ it constructs a complete original
   finite assignment $\mathbf x_h$ satisfying $\Phi$ and
   $\mu(t_i(\mathbf x_h))>h$ for every $i$.
3. **BARRIER:** $\operatorname{Sol}(\Phi)\ne\varnothing$, an original
   solution, and a computable natural $C$ such that
   $m_{\mathbf t}(\mathbf x)\le C$ for every original solution.

The bound is on the minimum of the designated depths. It is not claimed
optimal. The procedure does not need a supplied prefix, source-size
bound or physical budget.

Proof. Form the finite branch list of §2, with all output definitions,
and decide each branch's feasibility by NSF. If none is feasible,
Lemma 2.2 proves EMPTY in both source directions.

Otherwise inspect $A_b$ on each feasible branch. If some $A_b$ is empty,
use Lemma 3.4 on that branch. For a given $h$, choose

$$
k=\max(k_0,2h+2).
\tag{NLC.11}
$$

Every primitive leaf of every output is either an explicit free scalar
or lies inside one of the constant-rank markers: there is no anchored
output occurrence by the branch test. Hence its rank is at least $k$.
Formula (NLC.9) gives minimum native leaf depth at least
$\lfloor k/2\rfloor\ge h+1$ for every output. Lemma 3.4 supplies all
original variables and all constraints, proving DEEP with effective
finite witnesses for every requested $h$.

If every feasible branch has a nonempty anchor set, compute

$$
C=\max_{b\text{ feasible}} C_b.
\tag{NLC.12}
$$

Any original solution chooses one of these branches by Lemma 2.2.
Lemma 3.3 gives its bound $C_b\le C$, including original solutions
not belonging to any marker witness family. A feasible branch supplies
the promised original solution. This proves BARRIER.

The three outcomes are exhaustive and mutually exclusive: EMPTY has
no solutions, and choosing $h=C$ makes DEEP incompatible with BARRIER.
Termination uses only finitely many Boolean, collapse and negative
choices, finite shape unification, finite equation-graph calculations
and finite anchor inspection. No increasing-depth loop is used for the
classification, and no appeal to finite image, Dickson finiteness or
compactness supplies its stopping rule. The construction at (NLC.11)
is invoked only after the classification has already returned DEEP.
$\square$

**Corollary 4.2 (fixed observations and existential auxiliaries).** The
same exhaustive decision holds after exactly compiling any finite list
of fixed native observations, full-row conditions or guarded reached
output expressions. All original variables and all auxiliary witnesses
can be reconstructed.

Proof. NSF Lemma 5.1 supplies finitely many formula cases with both
source directions. Apply Theorem 4.1 to each case and its designated
native output terms. If a case is DEEP, its reconstruction supplies
original witnesses at every $h$. If all nonempty cases are BARRIER,
the maximum of their finitely many bounds bounds every original
solution in its own case. If all cases are EMPTY, the exact original
predicate is empty. Auxiliary variables are retained throughout;
existentially forgetting them changes neither a designated output nor
its reconstructed original source. $\square$

**Proposition 4.3 (distinctions from image infinitude and separate
unboundedness).** The all-depth question is different from each of the
following already decidable or weaker questions.

- The image of $\langle\alpha,z\rangle$, with $z$ unrestricted, is
  infinite, but its minimum leaf depth is always one.
- On $\Phi(x,y)=(x=\alpha\lor y=\alpha)$, each coordinate separately
  has unbounded minimum leaf depth, but $\min(\mu(x),\mu(y))=0$
  on every solution.
- On $\Phi(x,y)=(x=\alpha)$ with output tuple $(x,y)$, a barrier of
  zero bounds the tuple minimum while the size and minimum leaf depth
  of $y$ are unbounded.

Proof. Pair injectivity gives the infinite image in the first example,
and (NLC.2) gives depth one. In the second example use
$(T_{2h+2},\alpha)$ or $(\alpha,T_{2h+2})$ for the separate coordinates;
Lemma 3.1 gives their unbounded depths, while one coordinate is always
a leaf. The same atomic sequence proves the third assertion. These
examples separate the quantifiers of Theorem 4.1; they introduce no
alternative source interface or recovery task. $\square$

## 5. Exact finite-row contact at a supplied constructor context

**Definition 5.1 (context limit and original prefixes).** A finite
original constructor context $C$ is a finite ordered tree of pairs,
concrete leaves $\alpha,\beta$ and holes $\square_1,\ldots,\square_m$,
each occurring exactly once. Its hole addresses $p_1,\ldots,p_m$ are
distinct and prefix-free. Distinct hole names do not require different
values: all equalities and disequalities among their fillings come from
the full constraints. Let $d_C$ be the maximum depth of any node of this
finite context, including its holes and concrete leaves.

For describing limits only, allow finite or infinite ordered trees in
which each reached node is a leaf or has exactly two children. Replies
at missing addresses are $\mathsf{absent}$. Write $v\equiv_h w$ for
equality of their replies at every original-root word of length at
most $h$. Let $\Omega$ be the unique all-branch infinite tree, and set

$$
K_C=C[\Omega,\ldots,\Omega].
\tag{NLC.13}
$$

There is no infinite source in (NLC.4), and $K_C$ is never a register,
a source witness or an observer query. A finite tree is isolated by its
prefix through its maximum leaf depth. For a set $S$ of finite trees,
write $K\in\overline S$ to mean exactly
$\forall h\ \exists u\in S\ (u\equiv_h K)$. This is the only use of
prefix closure in the contact decision; its effectiveness will come
from §4, not from the notation.

**Definition 5.2 (exact row strata and supplied contact).** Fix two
distinct attained full-row labels $r_0,r_1\in R_Q(D)$ and put

$$
D_i=\{u\in D:R_Q(u)=r_i\}\qquad(i=0,1).
\tag{NLC.14}
$$

Their supplied-context contact is

$$
\operatorname{Contact}(C;r_0,r_1)\quad\Longleftrightarrow\quad
 K_C\in\overline{D_0}\cap\overline{D_1}.
\tag{NLC.15}
$$

All parts of each row label are imposed on the finite sources in
(NLC.14). No assertion requires $R_Q(K_C)$ to equal either label or
even defines a service target on $K_C$. Row attainment and distinctness
are effective preconditions: NSF checks each full-row stratum, while
the finite labels themselves can be compared directly. No finite
row-image promise on the rest of $D$ is needed.

**Lemma 5.3 (exact context decomposition near its limit).** Suppose
$m\ge1$.

1. If $u\equiv_H K_C$ and $H\ge d_C$, then there is a unique tuple
   $\mathbf z$ of finite original subtrees with $u=C[\mathbf z]$.
   Moreover $\mu(z_j)>H-|p_j|$ for every $j$.
2. If $u=C[\mathbf z]$ and $\mu(z_j)>h$ for every $j$, then
   $u\equiv_h K_C$.

Proof. In the first assertion, every explicit pair of $C$ is confirmed
by the prefix, and every explicit concrete leaf stops the source at
exactly that position with exactly that value. Every hole position is
reached, since its limit reply is branch. Take $z_j=u|_{p_j}$; induction
on the finite context proves the reconstruction and uniqueness. At
all suffixes of length at most $H-|p_j|$, the corresponding reply in
$z_j$ is branch. Definition 1.1 gives the depth inequality.

For the second assertion, follow any word of length at most $h$.
Outside holes its reached branch, concrete leaf or absent reply is
fixed by $C$. If it enters hole $j$, its remaining length is at most
$h$, so it sees a reached branch in $z_j$, just as in $\Omega$.
These cases exhaust all words, including words extending concrete
leaves. $\square$

**Lemma 5.4 (whole-source formula for a fixed labelled contact).** For
$m\ge1$, construct the following predicate on two independent tuples
of hole values:

$$
\Psi_C(\mathbf z^0,\mathbf z^1)\quad\Longleftrightarrow\quad
\bigwedge_{i=0}^1
\big(C[\mathbf z^i]\in D\ \land\ R_Q(C[\mathbf z^i])=r_i\big).
\tag{NLC.16}
$$

It has an effective finite native QF compilation with exact
reconstruction, and its designated output tuple is the nonempty tuple
of all $2m$ hole values. Then

$$
\begin{aligned}
&\operatorname{Contact}(C;r_0,r_1)\\
&\quad\Longleftrightarrow\quad
\forall h\ \exists\mathbf z^0,\mathbf z^1\quad
\left(\Psi_C(\mathbf z^0,\mathbf z^1)\ \land\
\bigwedge_{i=0}^1\bigwedge_{j=1}^m\mu(z_j^i)>h\right).
\end{aligned}
\tag{NLC.17}
$$

Proof. Substitute the finite context into every predicate defining each
stratum. NSF Lemma 5.1 compiles its fixed epoch/address observations,
whole guarded comparisons and complete old and target row tests. All
variables within one source copy retain their shared occurrences; the
two different original source copies use disjoint variable lists.
Both copies impose the same entire retained input. In particular a
negative relation is its two guards and its whole-tree inequality,
not the complement of a guarded equality.

The exact row compiler keeps the reached set, the full native mask of
the concrete exterior and every pairwise equality or disequality
specified by the partition. It retains uncut residual terms in the
mask. These are [NSF, Lemma 5.1][NSF] and [NPL, Lemma 5.2][NPL], with
the prescribed row values, not a relaxation to their partitions.
The finite prefix-case reconstruction returns $C[\mathbf z^i]$ with
all these predicates. Conversely every original tuple satisfying
(NLC.16) chooses its actual prefix cases. Thus both source-fiber
inclusions hold even when some cut addresses are absent, classes
repeat, or a constraint involves an off-task subtree.

If contact holds, for a given $h$ choose a source in each stratum
agreeing with $K_C$ through $H=h+d_C$. Lemma 5.3 gives its unique
context filling, with each depth greater than $h$. The two choices
combine in (NLC.16) because it has no extra relation between source
copies. Conversely a tuple in the right side of (NLC.17) gives a
source in each exact stratum and, by Lemma 5.3, both agree with $K_C$
through $h$. This proves contact at every $h$. $\square$

## 6. Exact termination for the supplied contact

**Theorem 6.1 (contact decision with finite witnesses or a finite
exclusion depth).** Under Definition 5.2 there is an effective
terminating decision of (NLC.15).

A YES answer gives, for every $h$, finite original witnesses
$u_h^0\in D_0$ and $u_h^1\in D_1$ with

$$
u_h^0\equiv_h K_C\equiv_h u_h^1,
\qquad R_Q(u_h^0)=r_0\ne r_1=R_Q(u_h^1).
\tag{NLC.18}
$$

A NO answer gives an effective finite $H$ and identifies at least one
$i\in\{0,1\}$ for which no member of $D_i$ agrees with $K_C$ through
$H$. This NO result concerns only the supplied context and row pair.

Proof. If $m=0$, then $K_C=C$ is finite. Agreement through $d_C$ forces
a finite source to be exactly $C$. It cannot have both distinct full
rows. Return NO with $H=d_C$, checking the two fixed-prefix stratum
queries to identify an excluded stratum.

For $m\ge1$, apply Corollary 4.2 to the exact formula (NLC.16) and all
its $2m$ designated hole values. In its DEEP case reconstruct the two
sources at each requested $h$. Lemma 5.4 proves YES and (NLC.18).

In its EMPTY case set $H=d_C$. If both strata had a source agreeing
with $K_C$ through $H$, Lemma 5.3 would provide two context fillings
satisfying (NLC.16), a contradiction. Hence one stratum is excluded.

In its BARRIER case let $C_0$ be the uniform bound on the minimum of
the $2m$ hole depths and set

$$
H=d_C+C_0.
\tag{NLC.19}
$$

If each stratum had a matching source through this $H$, Lemma 5.3
would yield fillings with
$\mu(z_j^i)>H-|p_j|\ge C_0$ for every $i,j$. Their joint tuple would
contradict the all-solutions barrier. Thus again at least one stratum
has an empty such neighborhood.

To identify it, query each entire stratum with the finite list of
literal replies of $K_C$ through the computed $H$. Every reply in
that list is computable from the finite context, so these are NSF's
fixed-navigation queries on original finite sources. At least one is
empty by the preceding argument. This final decision preserves all
signs, guards and full row labels. All classification steps terminate
by §4; the two final queries terminate by NSF. The construction does
not enumerate contexts or search for an unknown common limit. $\square$

**Corollary 6.2 (finite supplied families).** For any finite supplied
family of contexts and finite supplied family of attained row pairs,
one can decide which of their contacts hold and return the same
witnesses or exclusion depths for each. If the full row image is finite,
NPL Theorem 5.3 can supply the exact finite row list for this purpose.

Proof. There are finitely many instances of Theorem 6.1. Exact row
image enumeration is reused only when its finite-image decision has
that outcome. A finite list of negative contact answers does not range
over other contexts or other kinds of limit. $\square$

## 7. The actual paid-service obstruction

**Theorem 7.1 (all adaptive competitors excluded by a positive
contact).** Assume the authentic acquired input of Assumption 1.2.
If Theorem 6.1 returns YES, no legal controller of Definition 1.3 has
a uniform finite raw-read bound while recovering the full $R_Q$ on the
entire $D$. The conclusion allows arbitrary finite physical addresses,
reply-dependent serial updates, early and zero epochs, absent reads,
sourcewise finite computation and genuine absorbing halt.

Proof. The witnesses (NLC.18) show that no original prefix depth
determines $R_Q$ on $D$. Apply the serial/static/prefix existence
correspondence [ARH, (2.3)][ARH]. Its relevant hypotheses are common
complete state, four-valued replies, source-total termination and
original-prefix locality, all preserved here; its literal-only
source-language decision is not used.

For the direct all-comparator argument underlying that application,
suppose a legal $A$ has at most $K$ reads on every source. There are
finitely many realized reply histories of length at most $K$. From a
realized history, deterministic common control fixes the computation
and update segment up to the next read or halt. That segment is finite:
some original source realizes the history, and the controller terminates
on that source. Neither updates nor local computation introduce another
source observation. Consequently the realized executions form a finite
reply tree, with finitely many submitted physical words. Let $h$ be the
maximum of their lengths, taking $h=0$ if there are no reads.

Use the finite original witnesses (NLC.18) at this $h$. The native
locality supplier [NativeDepthPatterns, `original_prefix_locality`][DEPTH]
states that agreement of original replies through $|p|$ makes the
reply at $p$ equal at every common epoch. It includes originally
absent and subsequently born addresses. Inductively the two witnesses
therefore give the same next reply at the same actual epoch, the same
subsequent common control, and the same terminal output in the finite
reply tree. Their full row labels differ, a contradiction.

The finite reply tree in this contradiction need not be effectively
extracted from arbitrary controller code; the theorem quantifies over
every such realized tree. For a supplied finite controller tree its
maximum word length is directly available, and (NLC.18) constructs a
finite counterpair to that tree. No assumption bounds competing word
lengths or updates in advance. No actual action is performed on a limit
tree, and no reconstructed source is used as the unknown source.
$\square$

**Corollary 7.2 (resource consequences at a positive contact).** Under
the same hypotheses, every correct source-total controller has

$$
\sup_Dq_A=\infty,
\qquad \sup_D\ell_A=\infty.
\tag{NLC.20}
$$

For every rational nonnegative weight vector with
$\lambda_q+\lambda_\ell>0$, every correct controller has
$W_\lambda(A)=\infty$. If both observation weights vanish, the infimum
is zero and is attained by an existing static source-total recovery
service. These are scoped consequences of a positive contact, not a
decision of resources on every signed fiber.

Proof. The first claim is Theorem 7.1. The sourcewise cleanup in
[JRF, Lemma 3.2][JRF], whose all-source transfer is recorded by
[NSF, Proposition 7.4][NSF] and [NFO, §2][NFO], preserves replies,
termination and output and gives $q(u)\le\ell(u)+\max(0,2-N)$ without
increasing either coordinate or actual updates. It relies on repeated
same-epoch caching and the source-independent branch root at epochs
at least two, not on literal-only GB or WS2S. If $A$ had bounded
$\ell$, this cleanup would contradict Theorem 7.1. Thus both separate
suprema in (NLC.20) are infinite.

For a positive observation weight, the same-run nonnegative sum is at
least that weighted coordinate on every source; its supremum is
therefore infinite. No equality with a sum of coordinate suprema is
used. With only update weight, the existing historical-literal decoder
and finite original-tree traversal of [JRF, Theorem 7.1][JRF] recover
$u$ at the authentic static epoch $N$, compute its full $Q$ row and
halt, using zero actual updates. Each original tree is finite, so this
service is source-total; its unbounded read costs do not enter those
weights. Nonnegativity proves the zero minimum. $\square$

**Proposition 7.3 (acquisition and certificate boundaries).** The
negative consumer above preserves the original paid-input task. Its
witness pairs are not a replacement source domain, a free equality
query, or one finite sample refuting every budget.

Proof. Each constructed $u_h^i$ satisfies (NLC.4) with every guard,
old class and additional record, by Lemma 5.4. At a supplied public
acquisition schedule, [ARH, Proposition 2.1][ARH] produces exactly this
retained fiber under the complete handoff assumption. It traverses
finite actual subtrees, keeps their paid descriptions for comparison,
performs the actual forward updates and reaches $N$. Thus every such
finite witness can give the same stipulated retained data; conversely
every successful original source satisfies all those data. Acquisition
costs can vary without a uniform bound and are not cancelled by the
short retained signs.

Theorem 7.1 uses those sources to refute a proposed common post-cut
controller. It performs no post-cut comparison outside its legal
reads. The offline computation of a pair at depth $h$ is a mathematical
certificate operation, not an observation made by that controller.
Different $h$ or different finite controller trees can require
different finite pairs. [NFO, Proposition 8.1][NFO] still applies:
every finite source sample admits some finite static budget. There is
no quantifier exchange to a single finite sample obstructing all
budgets. $\square$

## 8. A recurrent anchored-leaf limit outside the context language

**Definition 8.1 (one acquired fiber and two exact labels).** Put
$F(y)=\langle\alpha,y\rangle$ and $U(x,y)=\langle x,\langle y,F(y)\rangle\rangle$.
Use the old root cut $P=\{\varepsilon\}$ and its one-hole row. Retain
exactly the literals

$$
(0,\varepsilon,\mathsf{branch}),\quad
(0,R,\mathsf{branch}),\quad
(0,RR,\mathsf{branch}),\quad
(0,RRL,\alpha)
\tag{NLC.21}
$$

and the positive whole-subtree record

$$
(0,RL,0,RRR,=).
\tag{NLC.22}
$$

Choose the original target $Q=\{L,RL,RR\}$. Let $r_0$ have the concrete
exterior $\langle\square_1,\langle\square_2,\square_3\rangle\rangle$
and partition $\{\{1,2\},\{3\}\}$; let $r_1$ have that same reached
set and exterior and partition $\{\{1,3\},\{2\}\}$. These labels
specify the full rows, with no unknown outside component. An authentic
handoff may occur at any $N\ge0$ after the stated records have been
acquired.

**Lemma 8.2 (entire original fiber and exact strata).** The complete
fiber of (NLC.21)–(NLC.22) is exactly

$$
D^*=\{U(x,y):x,y\in\mathcal T\}.
\tag{NLC.23}
$$

Its two designated whole-row strata are exactly

$$
\begin{aligned}
D_0^*&=\{U(y,y):y\in\mathcal T\},\\
D_1^*&=\{U(F(y),y):y\in\mathcal T\}.
\end{aligned}
\tag{NLC.24}
$$

Proof. The four literals decompose every original source as
$\langle x,\langle y,\langle\alpha,z\rangle\rangle\rangle$.
Both endpoints of (NLC.22) are reached there and its whole equality
says $y=z$. This gives (NLC.23). Conversely every displayed $U(x,y)$
has that old row, each literal and both reached equal endpoints.
The two inclusions retain the actual source, not just a tuple model.

At the target holes the complete subtree values are $x,y,F(y)$.
A finite tree $y$ cannot equal $F(y)$: the latter has one more leaf.
Therefore the first exact partition holds if and only if $x=y$,
and the second holds if and only if $x=F(y)$. All other cross-class
inequalities in those partitions follow from $y\ne F(y)$. The
reached set and concrete exterior are fixed on the entire fiber,
proving (NLC.24) and attainment of both labels. The acquired record
is a genuine whole-subtree link; it is not a literal-history substitute.
$\square$

**Definition 8.3 (anchored comb).** Let $K$ be the infinite tree with
branch nodes at every $R^j$ and an $\alpha$ leaf at every $R^jL$,
for $j\ge0$, and no other reached positions. Equivalently it is the
unique finite-or-infinite tree solving

$$
K=F(K)=\langle\alpha,K\rangle.
\tag{NLC.25}
$$

Let $y_0=\beta$ and $y_{n+1}=F(y_n)$. These are finite original trees.
For $n\ge1$ they have $\mu(y_n)=1$, despite unbounded maximum depth.
Set

$$
L^*=\langle K,\langle K,K\rangle\rangle.
\tag{NLC.26}
$$

Uniqueness in (NLC.25) follows by successively inspecting the right
child and its left leaf; every finite address is either one of those
specified positions or extends such a leaf. No finite tree solves it,
by the leaf-count argument in Lemma 8.2.

**Theorem 8.4 (unique labelled common limit and incompleteness for this
row pair).** The two exact strata in (NLC.24) have exactly one common
prefix-closure point:

$$
\overline{D_0^*}\cap\overline{D_1^*}=\{L^*\}.
\tag{NLC.27}
$$

They have finite original same-prefix/different-row witnesses at every
depth. Nevertheless no finite original constructor context $C$ with
all its holes filled by $\Omega$ satisfies
$\operatorname{Contact}(C;r_0,r_1)$ for this row pair.

Proof. Any prefix limit of either stratum retains the finite outer
constructor skeleton. In the first stratum its left subtree equals
the right-left subtree. Equality of two whole trees is closed under
prefix agreement: if the limiting subtrees differed, some finite
address would witness different replies, contradicting their equal
finite approximants. In the second stratum the left subtree equals
$F$ applied to the right-left subtree. This relation is also closed:
its root pair, left $\alpha$ and equality of the right subtree to the
argument are each forced by finite addresses. The relation between
the right-right and right-left subtrees, already imposed in every
$U(x,y)$, has the same property.

Consequently a common limit must have the form $U(x,y)$ as a
finite-or-infinite constructor expression, with $x=y$ from the first
label and $x=F(y)$ from the second. Hence $y=F(y)$, so $y=K$ by
Definition 8.3 and the common limit is (NLC.26). This proves that the
intersection is contained in the displayed singleton; no assertion
about continuity of a finite equality partition was used.

Conversely take the finite sources

$$
u_n^0=U(y_n,y_n),\qquad
u_n^1=U(y_{n+1},y_n).
\tag{NLC.28}
$$

They lie in their exact strata by Lemma 8.2, so they satisfy every
acquired constraint with both guards. At every depth less than $n$,
$y_n$ and $y_{n+1}$ agree with $K$: their terminal $\beta$ leaves are
still beyond that depth. The constructors of $U$ preserve this
agreement. For any $h$, taking $n>h$ therefore makes both displayed
sources agree with $L^*$ through $h$ and with each other. Their finite
full rows remain $r_0$ and $r_1$. This proves membership of $L^*$ in
both closures and the finite witness assertion.

The tree $L^*$ is infinite and has no subtree equal to $\Omega$.
Indeed every subtree of $K$ is either $K$ or an $\alpha$ leaf, and
both contain a reached leaf. The remaining subtrees of $L^*$ are
$L^*$ itself and $\langle K,K\rangle$, which also contain a reached
leaf. By contrast any infinite $C[\Omega,\ldots,\Omega]$ has at
least one hole and therefore has a subtree exactly $\Omega$ at its
hole address. A context with no holes is finite. Thus no such context
represents $L^*$, and (NLC.27) excludes every supplied-context contact
for the prescribed pair. $\square$

**Proposition 8.5 (the limitation is pair-specific).** The preceding
example does not make $D^*$ invisible to every context certificate.
Its complete row image has exactly three labels: $r_0,r_1$ and a third
label $r_2$, with the same reached set and exterior and the all-distinct
partition. Its source fiber is infinite. The pair $(r_0,r_2)$ does have
a finite-context contact.

Proof. Since $y\ne F(y)$, the only three possible partitions of
$x,y,F(y)$ are the stated ones. The first two are attained by Lemma 8.2;
the third is attained by the witnesses below. Increasing the size of
$y$ in $U(y,y)$ gives infinitely many sources. The third exact stratum
consists of the $U(x,y)$ with $x\ne y$ and $x\ne F(y)$. Consider

$$
C^\dagger=
 \langle\square_1,
   \langle\square_2,\langle\alpha,\square_3\rangle\rangle\rangle.
\tag{NLC.29}
$$

For $m\ge4$, use $U(T_m,T_m)$ in $D_0^*$ and
$U(T_{m+1},T_m)$ in the third stratum. The two atomic trees are
unequal by ABC's rank injectivity. Also $T_{m+1}\ne F(T_m)$:
the former has left child $T_m$, which is a branch, whereas the
latter has left child $\alpha$. Thus the second source has exactly
$r_2$, not merely a row different from $r_0$.

Their three fillings of $C^\dagger$ are respectively
$(T_m,T_m,T_m)$ and $(T_{m+1},T_m,T_m)$. By Lemma 3.1 all those
minimum leaf depths tend to infinity. Lemma 5.3 proves contact at
$C^\dagger[\Omega,\Omega,\Omega]$. Both witnesses retain the repeated
$y$ enforced by the acquired link. Therefore Theorem 8.4 establishes
incompleteness for the fixed pair $(r_0,r_1)$ only. It neither supplies
a fiber escaping all row pairs nor a new undecidability theorem.
$\square$

## 9. Reuse, finite approximability and the remaining uniform question

**Proposition 9.1 (exact supplier separation).** The new implication
proved here is

$$
\begin{aligned}
&\text{finite native normal branches with all-solution factorization}\\
&\quad\Longrightarrow
 \text{simultaneous minimum-depth barrier or finite witnesses at all depths}\\
&\quad\Longrightarrow
 \text{exact contact decision for a supplied finite constructor context}\\
&\quad\Longrightarrow
 \text{finite original counterpairs against every bounded legal service
 in each YES case}.
\end{aligned}
\tag{NLC.30}
$$

This implication has the following reuse boundaries.

| Supplier | Exact use and retained limit |
| --- | --- |
| [ABC, §§2–4][ABC] | All-source normal-code conjugacy, native rank translation, exact expansion and mask interpretation. The proof uses its normal subdomain; it does not replace it by ambient free terms. |
| [NSF, §§2–5][NSF] | Finite native feasibility, original-solution branch factorization, shape markers, scalar/block offset separation and exact guarded compilation. A fixed formula's marker witnesses are not all solutions and do not bound depth for changing prefix formulas. |
| [NSF, §§6–10][NSF] | Supplied-prefix decision, bounded boxes and their consumers, plus forward-closed fibers and exact invariant charts under their hypotheses. Theorem 4.1 imposes no forward-closure or chart-invariance condition on the QF input. |
| [NPL, §§2–5][NPL] | Anchored/free scalar data, marker witnesses, all-solution rigidity and exact finite/infinite output-image classification, including full rows and original witnesses. Infinite image does not imply simultaneous minimum-depth growth, as Proposition 4.3 shows. |
| [NPL, §§6–8][NPL] | Exterior limitedness, whole-source finiteness and actual entire-finite-fiber Pareto/weighted services. A finite image or a finite witness list is not an observable partition selector on an infinite fiber. |
| [NFO, §§3–7 and 8.1–8.4][NFO] | Arbitrary-word decisions at prescribed budgets, finite-source obstruction completeness for each such budget, exact rational thresholds including zero weights and conditional complete optimization after finite success. No all-budget finite sample follows; the outer existential stopping problem remains separate. |
| [ARH, §§1–3][ARH] | Entire acquired signed fiber, paid producer and serial/static/prefix existence equivalence on it. The all-comparator argument uses its operational hypotheses, not an unsupported general source-language decision. |
| [JRF, §§2–3][JRF] | Universal sourcewise nonexpansive late probes, actual update capping and read cleanup. Its literal-only GB and matched WS2S decision in §§4–7 are not transferred to arbitrary signed fibers. |
| [URR, Theorem 3.1, Corollaries 3.2–3.3 and Theorem 5.1][URR] | A rank-independent residual tuple and exact rank support for negative mixed templates over a full Cartesian residual domain; an entire acquired family where that premise is independently proved. No arbitrary positive residual normalizer or whole-source representative theorem is supplied. |

Proof. The first line of (NLC.30) is the supplier input in Lemma 2.2.
Lemmas 3.3–3.4 add a universal anchored bound and a simultaneous
free-rank ray; neither the universal bound nor its simultaneous converse
follows from image infinitude. Theorem 4.1 makes their alternative
terminate. Lemmas 5.3–5.4 give both exact finite-source directions for
its supplied-context application. Theorem 7.1 then uses original-prefix
locality and the entire legal service class. These prove the displayed
chain without changing the original row or operations.

URR can be reused after an independent positive correspondence gives
its unrestricted Cartesian residual domain. Here arbitrary positive
equations and fixed-navigation guards are retained and solved in the
NSF branches; they are not presumed to have that domain. URR's one
fixed tuple realizes negative constraints uniformly in its rank
parameters. Such a tuple need not make a designated residual's minimum
leaf depth large, and it need not satisfy a newly imposed positive
residual equation, as URR Proposition 7.1 already demonstrates. The
ray in Lemma 3.4 changes witnesses with $h$ after all positive branch
relations have been enforced. It is consequently not a relabeling of
URR's fixed section or a claim to represent every source. $\square$

**Open problem 9.2 (unrestricted recovery and complete signed finite
approximability).** For arbitrary nonempty (NLC.4), retain the original
question from [NFO, Open problem 8.4][NFO]: decide

$$
\exists K\ \operatorname{Win}_D(K,U)
\quad\Longleftrightarrow\quad
\exists h\ \operatorname{PrefDet}(D,Q,h),
\qquad U=\max(0,5-N).
\tag{NLC.31}
$$

Here $\operatorname{Win}_D(K,U)$ requires a legal correct service with
$q_A(u)\le K$ and $a_A(u)\le U$ for every $u\in D$, permitting arbitrary
finite physical words. The universal all-source cap supplies this update
allowance. The predicate $\operatorname{PrefDet}(D,Q,h)$ says that any two
members of $D$ agreeing on all original replies through depth $h$ have
the same complete $Q$ row.
NSF already decides each supplied $h$, and NFO each supplied $K$.
A succession of negative answers does not decide the existential.

When NPL gives a finite full-row image on an infinite source fiber,
Theorem 6.1 decides one additional kind of exact cross-row contact,
with a finite negative stopping rule for each supplied context. It does
not give a complete finite list of context limits to test. Theorem 8.4
rules out completeness for every prescribed row pair within this
context language: an anchored leaf can recur indefinitely along a
common limit. Proposition 8.5 prevents strengthening that example to
a claim that the entire fiber evades all context certificates.

The remaining signed finite-approximability obligation is to decide
which joint prefix behaviors of two different exact finite-row strata
have original finite witnesses at every depth, retaining all native
positive equations, negative equations and both guards. An assignment
of infinite trees satisfying selected limiting equalities is not such
a certificate: finite signs or distinct row labels may coalesce at its
limit. In (NLC.28) the two finite labels approach a tree whose three
reached target subtrees are all equal. The finite labels must therefore
be carried by their actual finite approximants, as in (NLC.18), rather
than recovered from that ideal partition.

Neither arbitrary mixed constructor/atomic closure, an effective
complete certificate language, nor a general negative stopping rule
for (NLC.31) is proved here. Conditional resource optimization remains
available from NFO after a finite success; a contact YES supplies the
scoped infinite-observation-price conclusion of Corollary 7.2. No
global novelty, priority, undecidability or completion of the
unrestricted minimal-relations programme is asserted.

## 10. Mathematical sources and evidence boundaries

**References 10.1 (repository and pinned upstream interfaces).** The
following interfaces give the precise correspondence to existing
formal source; their source statements do not certify a new compiled
application of this companion.

| Source | Existing statement and applicability |
| --- | --- |
| [NativeDepthPatterns][DEPTH], `original_prefix_locality`, `depthEquiv`, private `fill_decompose` and `decompose_fill` | Reply locality at every common epoch from the original prefix through the physical word length; exact original finite-pattern/frontier reconstruction. These are the source and action interfaces in §§5–7. |
| [NativeGroundSeparation][GROUND], including private `count_length`, `evaluated_length`, `compound_mass_ne`, `bounded_eval_injective` and public `simultaneous_ground_separation` | Equal-mass separation for finite Boolean free-magma terms with a fixed finite syntax bound. NSF supplies the distinct nonleaf one-constant shape markers used in Lemma 2.2; no new ground-separation theorem is claimed. |
| [NativeCutFibers][CUT], `rowFiberEquiv`, private `recover_fill` and `fill_injective` | Both directions of the full old-row source correspondence, including shared classes and all class disequalities. A mathematical inverse on a supplied source is not an observer port. |
| [NativeHistoryCells][HISTORY], `cell_feasibility_exact`, `historyCellEquiv`, private `syntax_iff_ground` and `feasible_history` | Exact literal-history cells. Its history is a list of epoch/address/reply records. Arbitrary signed whole-subtree comparison feasibility here comes from NSF, not from changing that formal history sort. |
| [NativeSymbolicRecutting][RECUT], `symbolic_recut_exact`, private `termAt_fill` and `exterior_commute` | Full original reached order, exterior and pairwise partition after filling. These fields are all retained in the exact row strata. |
| [Pinned mathlib, `FreeMagma`][FREE] | `of`, `mul`, decidable equality, `lift` and `length_pos` for free finite binary trees. The source parameters are $\alpha=\mathtt{of\ true}$, $\beta=\mathtt{of\ false}$ and pairing $\mathtt{mul}$; the native $\rho$ still requires its interpreted leaf laws. |

The formal observer interfaces do not state a simultaneous minimum-depth
alternative for arbitrary native QF signed constraints. Theorem 4.1's
additional branch inference and Theorem 6.1's exact contact reduction
are ordinary repo-derived results. Their all-solution direction is not
inferred from the existence of a finite marker family.

**References 10.2 (primary literature and scope).** H. Comon and
P. Lescanne, [*Equational Problems and Disunification*][CL], §3.2
Proposition 2 and Lemma 1, Appendix B.3, and §6.2 distinguish finite
and rational free-term algebras from general equational theories.
Their nontrivial syntactic disequation lemma uses infinite ground sort
carriers; Appendix B.3 uses the finite, in its one-variable induction
at-most-one, solution property. Section 6.2 explicitly withholds the
preceding results for general equational theories. These are
literature-attested elimination and separation methods. They do not
justify using a free occurs check on native interpreted $\rho$:
$\rho\beta=\langle\beta,\alpha\rangle$ is an actual finite solution
of a feedback equation that such a replacement would mishandle.

This companion uses syntactic unification only after NSF's exact normal
branch reduction, on its free shape terms, and uses native rank
translation for its all-depth witnesses. Rational-tree equations such
as (NLC.25) describe prefix limits, but no rational-tree solution is
used to assert finite satisfiability of signed native rows. The finite
sources in (NLC.28) establish that property separately.

The bounded source comparison is the listed native repository
suppliers, their public and private observer interfaces, pinned
`FreeMagma` source and the cited primary disunification passages.
It does not establish literature-wide originality or the nonexistence
of another unrestricted decision method. Lemmas 3.3–3.4, Theorems
4.1 and 6.1, and the fixed-row-pair boundary in Theorem 8.4 are classified
as repo-derived ordinary results. The normal-code correspondence,
finite feasibility, image classification, fixed-budget decisions and
paid serial/static equivalence are credited reusable suppliers.

**Convention 10.3 (verification boundary).** All new statements in this
volume are ordinary mathematics with the stated source, action and
handoff assumptions. Source inspection, document structure and
finite examples are separate from Lean kernel verification and from
actual paid physical execution. No solver, experiment, new runtime
observation mechanism or source-size promise accompanies the results.

[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NFO]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FINITE_OBSTRUCTION.md
[JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[URR]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[DEPTH]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[GROUND]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSeparation.lean
[CUT]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[HISTORY]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[RECUT]: https://github.com/the-omega-institute/trureturing/blob/cdf8955c35033409ca3e51aa485794bf57a78723/D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean
[FREE]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Free.lean
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf

## 追加锚（本行以下为增补区）

## 11. A prescribed row pair with no ordinary regular common limit

**Definition 11.1 (shifted input and ordinary regular trees).** The symbols
$D,U,K,r_i$ in §§11–12 are local to these sections. Retain the native
laws (NLC.1), the inclusive four-reply prefixes of Definition 5.1, and
Assumption 1.2 with an authentic common handoff $N\ge1$. Take the old
cut $P=\{\varepsilon\}$ and its complete row: one reached hole, exterior
$\square_1$ and singleton partition. The entire retained history is

$$
\begin{aligned}
H_0={}&\{(0,\varepsilon,\mathsf{branch}),
 (0,R,\mathsf{branch}),(0,RR,\mathsf{branch}),(0,RRL,\alpha)\},\\
H_{\rm rel}={}&\{(0,RRR,1,RL,=)\}.
\end{aligned}
\tag{NLC.32}
$$

Both endpoints of the positive record must be reached. There are no
further records in this instance. Let $D$ be the entire fiber (NLC.4)
of these data, and put

$$
G(y)=\langle\alpha,\rho(y)\rangle,\qquad
U(x,y)=\langle x,\langle y,G(y)\rangle\rangle,\qquad
Q=\{L,RL,RR\}.
\tag{NLC.33}
$$

Use that order for the target holes. The full labels $r_0,r_1,r_2$ all
have reached set $Q$ and numbered exterior
$\langle\square_1,\langle\square_2,\square_3\rangle\rangle$; their
partitions are respectively

$$
\{\{1,2\},\{3\}\},\qquad
\{\{1,3\},\{2\}\},\qquad
\{\{1\},\{2\},\{3\}\}.
\tag{NLC.34}
$$

Write $D_i=\{u\in D:R_Q(u)=r_i\}$, retaining every field of the row.

An ordinary regular, or rational, tree is a finite-or-infinite ordered
tree over the ranked signature $\alpha:0,\beta:0,\langle\, ,\,\rangle:2$
having only finitely many distinct rooted subtrees. This is the
literature-attested definition in [Comon–Lescanne, §2.1, pp. 4–5][CL],
with their child positions $1,2$ identified with $L,R$, and with no
variables. A missing position supplies the reply $\mathsf{absent}$;
it is not another constructor. Equality retains both labels and order.
Equivalently such a tree unfolds a finite rooted constructor graph:
each graph vertex supplies at most one subtree, and conversely the
finitely many subtree types supply vertices with their actual ordered
child edges. This representation does not add $\rho$ as a free
constructor.

**Theorem 11.2 (the entire shifted fiber and all three exact strata).**
The data (NLC.32) have precisely the source fiber and row strata

$$
\begin{aligned}
D&=\{U(x,y):x,y\in\mathcal T\},\\
D_0&=\{U(y,y):y\in\mathcal T\},\\
D_1&=\{U(G(y),y):y\in\mathcal T\},\\
D_2&=\{U(x,y):x,y\in\mathcal T,\ x\ne y,\ x\ne G(y)\}.
\end{aligned}
\tag{NLC.35}
$$

All three rows are attained, and these are the entire row image.

Proof. The four literals decompose each source uniquely as
$u=\langle x,\langle y,\langle\alpha,z\rangle\rangle\rangle$.
Its original subtree at $RRR$ is $z$. The actual leaf and pair laws give

$$
\rho(u)=
 \langle\rho(x),\langle\rho(y),\langle\beta,\rho(z)\rangle\rangle\rangle.
\tag{NLC.36}
$$

Thus the epoch-one subtree at $RL$ is $\rho(y)$, and both compared
endpoints are reached. The retained whole-subtree equality is exactly
$z=\rho(y)$, proving the forward inclusion in (NLC.35). Conversely every
finite $U(x,y)$ has the complete old root row, the four stated literal
replies and both reached equal endpoints. Recovering $x=u|_L$ and
$y=u|_{RL}$ is inverse to this parameterization. It is a mathematical
inverse, not an observer operation. No finite source satisfying the
original input has been omitted.

Let $\ell(t)$ count leaves and $b(t)$ count $\beta$ leaves. The native
laws give $\ell(\rho(t))=\ell(t)+b(t)$ by induction. Consequently

$$
\ell(G(y))=1+\ell(y)+b(y)>\ell(y),\qquad y\ne G(y)
 \quad(y\in\mathcal T).
\tag{NLC.37}
$$

The entire target values are $(x,y,G(y))$. Their fixed geometry and
(NLC.37) give exactly the three alternatives in (NLC.35), including
every cross-class inequality. The first two rows are attained for
every finite $y$; $U(\alpha,\beta)$ attains the third. In particular
$D$ is nonempty and is not replaced by $D_0\cup D_1$.

The acquisition correspondence is [ARH, Proposition 2.1][ARH] applied
to exactly these coordinates: acquire the epoch-zero data and the
whole $RRR$ description by paid finite traversal, advance the same
register, acquire the epoch-one $RL$ description, compare the paid
descriptions, and continue to the common $N$. Under the complete cut
of Assumption 1.2, the successful retained output has exactly the
fiber just calculated, in both directions. Source-dependent traversal,
timing, cache and control information is subject to that same cut;
the calculation does not establish physical erasure or free equality.
$\square$

**Theorem 11.3 (native prefix bridge and the shifted fixed tree).**
On the finite-or-infinite trees of Definition 5.1, interpreted $\rho$
has a unique extension by its actual leaf replacements and pair law.
For inclusive depths $h\ge0$ it satisfies

$$
s\equiv_h t\ \Longrightarrow\
 \rho(s)\equiv_h\rho(t)
 \quad\hbox{and}\quad
 G(s)\equiv_{h+1}G(t).
\tag{NLC.38}
$$

There is exactly one tree $K$ with $K=G(K)$. Writing
$T_j=\rho^j\alpha$, its right spine and complete left subtrees satisfy

$$
K|_{R^j}=\rho^j(K),\qquad K|_{R^jL}=T_j
 \quad(j\ge0).
\tag{NLC.39}
$$

This $K$ is infinite and is not ordinary regular.

Proof. At a finite address in the image, follow the address through
original pairs until the first original leaf, if any. Thereafter the
reply is determined inside that leaf's specified finite image. If no
leaf occurs along the address, the image node is a pair. This defines
every reply consistently with the constructor arities and gives the
unique extension. It also proves that the image reply uses only
original replies at prefixes of the requested address. Matched leaves
produce the same born positions and the same absent replies; absence
at one epoch is not assumed to persist at the next. Equivalently,
induction on $h$ treats equal root leaves by their identical entire
images and equal pairs by their two children. This proves the first
part of (NLC.38), and the added pair in $G$ proves the second.
On finite sources this is the locality argument of
[ARH, Lemma 19.2][ARH]; the address argument here also covers infinite
branches.

Use the atomic identities and index injectivity of [ABC, Definition
1.3][ABC]. Define $K$ by a branch at every $R^j$ and the entire finite
subtree $T_j$ at $R^jL$. The tooth addresses are prefix-free.
Every finite word is either $R^j$ or $R^jLw$, so this definition fixes
all four replies, including absent suffixes inside a tooth.
Applying $\rho$ shifts each tooth to $T_{j+1}$; hence the right tail
is $\rho(K)$ and $K=\langle\alpha,\rho(K)\rangle$.

For any fixed tree $J=G(J)$, the native pair law gives
$\rho^j(J)=\langle T_j,\rho^{j+1}(J)\rangle$. Induction down its
right spine forces (NLC.39) with $J$ in place of $K$. The same
finite-word decomposition then forces $J=K$. Formula (NLC.37)
excludes a finite fixed tree. Finally the actual subtrees $T_j$ at
$R^jL$ are pairwise distinct by atomic index injectivity. Thus $K$
has infinitely many distinct constructor subtrees. Its right-spine
subtrees are also pairwise distinct, since their left children differ.
This uses the original constructor signature throughout. $\square$

**Theorem 11.4 (singleton nonregular contact for the prescribed pair).**
For the entire input (NLC.32), put $L=\langle K,\langle K,K\rangle\rangle$.
Then

$$
\overline{D_0}\cap\overline{D_1}=\{L\},\qquad
L\ \hbox{is not ordinary regular}.
\tag{NLC.40}
$$

For every inclusive depth $h$ there are actual finite sources
$u_h^0\in D_0$ and $u_h^1\in D_1$ with
$u_h^0\equiv_h L\equiv_h u_h^1$. Consequently the assertion that
every prescribed pair of distinct attained full rows with finite
same-prefix witnesses at all depths has an ordinary regular common
limit is false.

Proof. First prove that any common closure point is $L$, using the
architecture of Theorem 8.4. A closure point retains the finite
outer skeleton forced by (NLC.32). Equality of two subtrees at fixed
reached positions is closed under original prefixes: a failed
equality has a finite-address distinguishing reply. The graph of
$\rho$, and therefore that of $G$, is also closed by (NLC.38).
Indeed any difference at depth $d$ can be checked from finitely many
argument and output replies through depth $d$; choosing an original
prefix deeper by the fixed coordinate lengths tests those replies.

Every point in either closure therefore has the form $U(x,y)$ with
finite-or-infinite $x,y$. Membership in $\overline{D_0}$ forces $x=y$;
membership in $\overline{D_1}$ forces $x=G(y)$. A common point has
$y=G(y)$, so Theorem 11.3 forces $x=y=K$ and the point is $L$.
Only equalities were passed to the limit, not the finite disequalities
or their partition.

For the reverse inclusion and finite productivity, set

$$
y_0=\beta,\qquad y_{n+1}=G(y_n),\qquad
u_h^0=U(y_n,y_n),\qquad u_h^1=U(y_{n+1},y_n),
 \quad n=h+1.
\tag{NLC.41}
$$

Induction using the actual pair law shows that $y_n$ has teeth
$T_0,\ldots,T_{n-1}$ at $L,RL,\ldots,R^{n-1}L$ and terminal subtree
$\rho^n\beta=T_{n+1}$ at $R^n$. For any word of length less than $n$,
either it remains on the shared branch spine, or it first enters one
of the identical complete teeth. In the latter case its remaining
reply, whether leaf, branch or absent, is identical. Such a word
does not reach the terminal subtree. Thus $y_n\equiv_h K$ and
$y_{n+1}\equiv_h K$ when $n=h+1$. Constructors and (NLC.38) now give
both displayed sources' agreement with $L$ through $h$.

All these trees are finite. Theorem 11.2 places the two sources in
the entire original $D$, with every literal, both reach guards and
the mixed-epoch equality, and gives exactly the distinct full rows
$r_0,r_1$. In particular $y_n\ne G(y_n)$ retains every required
finite inequality. This proves membership of $L$ in both closures.
Since $L|_L=K$, Theorem 11.3 makes $L$ nonregular and excludes every
ordinary regular common-contact tree for this prescribed pair.

The three ideal subtrees at $Q$ in $L$ coincide. Their one-class
partition is neither finite label in (NLC.41), and cannot replace
those labels. Also $\mu(y_n)=1$ for $n\ge1$: this approximation is
not an assertion of growing minimum leaf depth. $\square$

## 12. Other-pair contact, finite descriptions and the exact boundary

**Proposition 12.1 (an ordinary context contact on the same entire fiber).**
The pair $(r_0,r_2)$ of Definition 11.1 has the regular common limit

$$
M=\langle\Omega,\langle\Omega,\langle\alpha,\Omega\rangle\rangle\rangle
  =C^\dagger[\Omega,\Omega,\Omega],
\tag{NLC.42}
$$

where $C^\dagger$ is the finite context (NLC.29).

Proof. For $m\ge4$ take $a_m=U(T_m,T_m)$ and
$b_m=U(T_{m+1},T_m)$. The first has row $r_0$.
For the second, $T_{m+1}\ne T_m$ by index injectivity, and
$T_{m+1}=\langle T_m,T_{m-1}\rangle$ has a branch as left child,
whereas $G(T_m)=\langle\alpha,T_{m+1}\rangle$ has an $\alpha$ leaf.
Thus the second has exactly $r_2$. Both belong to the same entire
$D$, retaining the original guarded link.

Their fillings of $C^\dagger$ are respectively
$(T_m,T_m,T_{m+1})$ and $(T_{m+1},T_m,T_{m+1})$.
By Lemma 3.1, $\mu(T_j)=\lfloor j/2\rfloor$; for any $h$, choosing
$m\ge2h+4$ makes every displayed filling agree with $\Omega$ through
$h$. Lemma 5.3 then gives $a_m\equiv_h M\equiv_h b_m$.
The tree $\Omega$ has one subtree type and a finite constructor
context adds only finitely many more, so $M$ is ordinary regular.
The third row has not been discarded. Theorem 11.4 therefore refutes
completeness required for every prescribed pair; it does not refute
a method permitted to choose another opposite pair in this fiber.
$\square$

**Proposition 12.2 (finite interpreted and parameterized descriptions).**
The nonregular $K$ still has its finite interpreted specification
$K=\langle\alpha,\rho(K)\rangle$. It also has the finite parameterized
constructor specification

$$
H(a,b)=\langle a,H(b,\langle b,a\rangle)\rangle,\qquad
K=H(\alpha,\beta).
\tag{NLC.43}
$$

Proof. For any finite trees $a,b$, let $A_0=a$, $A_1=b$ and
$A_{j+2}=\langle A_{j+1},A_j\rangle$. Define $H(a,b)$ to be the
right-infinite spine with entire left subtree $A_j$ at $R^jL$.
This defines all finite-address replies and satisfies the displayed
recursion. Conversely each right step in that recursion fixes the
next pair of parameters and the next complete tooth, so it uniquely
specifies that tree. For $(a,b)=(\alpha,\beta)$, the atomic recurrence
gives $A_j=T_j$ for every $j$; hence its output is exactly the $K$
of (NLC.39), including absent replies below teeth. Its infinitely many
different actual parameter values distinguish this specification
from a finite system of nullary constructor-graph states. The first
specification has the existence and uniqueness proof in Theorem 11.3.
$\square$

**Convention 12.3 (sources, consumed boundary and residual question).**
Theorems 11.2–11.4 and Proposition 12.1 give a concrete source and
parameter correspondence for the published shifted-context family of
[SPC, Theorems 3.2–3.3, 4.2 and 5.2][SPC]. Take its proper one-hole
context $C[t]=\langle\alpha,t\rangle$, hole word $R$ and shift $a=1$.
Its $F(y)$ is exactly (NLC.33)'s $G(y)$, so its source $U$, three full
rows, fixed point and common contact are the ones displayed here.
The positive record in (SPC.13) reverses the two endpoints of the
equality in (NLC.32); both reach guards are identical. Its additional
negative $y\ne G(y)$ holds on every finite assignment by (NLC.37).
Consequently its entire fiber equals the one in (NLC.35), even though
the literal retained record lists differ. This is equality of the
mathematical source fibers, not an identification of acquired physical
states or an uncharged acquisition of the additional record.

The singleton nonregular prescribed-pair contact and the other-pair
regular alternative are therefore applications of those existing
results, not new general contact theorems. The explicit four-reply
tooth description (NLC.39), finite indices (NLC.41) and two-parameter
constructor specification (NLC.43) supply the concrete correspondence
and richer finite description. Theorem 8.4's unshifted comb has only
itself and $\alpha$ as subtrees and is regular; allowing ordinary regular
limits covers that earlier pair. The interpreted shift in (NLC.32)
forces all distinct $T_j$ teeth in this specialization. Both source
descriptions retain Open problem 9.2's unrestricted stopping obligation.

Atomic recurrence and index injectivity are reused from ABC, native
finite locality and acquisition from ARH, and exact finite feasibility,
guarded compilation and supplied-depth decisions from
[NSF, Theorems 4.3, 5.2 and 6.1][NSF]. These finite decisions are not
a stopping rule for their outer existential. NSF §§9–10 retain their
closure and chart-invariance hypotheses: this $D$ is not globally
forward-closed, since its required $RRL$ leaf changes from $\alpha$
to $\beta$. In the direct constructor chart
$\langle x,\langle y,\langle\alpha,z\rangle\rangle\rangle$ with
$z=\rho(y)$, simultaneous residual $\rho$ preserves that equation
but not the target bit $x=\langle\alpha,z\rangle$: its true left side
becomes $\langle\beta,\rho(z)\rangle$. Eliminating $z=\rho(y)$ also
does not by itself supply ARH's synchronous target comparisons;
$x=G(y)$ still compares a variable with a nonground pair. The retained
record is not a whole-root/proper-descendant certificate, and ARH's
separate one-parameter graph $\langle\rho(y),y\rangle$ is not this
two-parameter fiber. These observations assert no failure of every
alternative chart or recognizer.

Comon–Lescanne supplies the ordinary rational-tree definition and the
free-constructor setting, not the native bridge (NLC.38), finite
signed approximants or a theorem about interpreted $\rho$ equations.
The source comparison is bounded to the cited suppliers and that
primary definition; no literature-wide novelty or priority is asserted.

Excluding ordinary finite constructor graphs at the contact point
does not exclude finite recursive, transducer or indexed certificates,
regular tree languages, effective search or all finite formalisms.
Every finite approximant here is itself regular, and (NLC.43) is a
finite richer description of the nonregular limit. Such a description
does not establish a generally complete or decidable certificate
language. Infinite trees remain auxiliary prefix-completion points,
never admissible native sources or physical registers.

Open problem 9.2, including the general arbitrary-signed
$\exists h\,\operatorname{PrefDet}(D,Q,h)$ decision and its negative
stopping obligation, remains unresolved by this increment. Additional
retained constraints would define another fiber and require their
own approximation proof. No undecidability result or additional
observer reset, equality, selector or cost port follows. All statements
retain the ordinary mathematical and handoff boundaries of
Definitions 1.1–1.3 and Convention 10.3.

[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md

## 追加锚（本行以下为增补区）
