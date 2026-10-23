# Atomic accumulation bases for complete relational observation

> This volume is reference mathematics, with ordinary proofs conditional on
> the stated suppliers; it asserts no Lean kernel verification. Its claim
> format is compatible with `generic-v1`. Once integrated, existing text and
> numbering remain fixed; corrections and additions follow the final append
> anchor. The mathematical increment is the exhaustive synthesis in §§3–4,
> its actual mixed-source application in §5, and the conditional recovery
> interface in §6. These are `repo-derived` ordinary inferences, with the
> literature and unrestricted-domain boundaries specified in §7.

## 1. Complete sources and the selected joint question

**Definition 1.1 (native trees and inclusive prefixes).** The source domain is
the nonempty finite free ordered tree algebra

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_n&=\rho^n\alpha\qquad(n\in\mathbb N).
\end{aligned}
\tag{AAB.1}
$$

Addresses are words over $\{L,R\}$, with root $\varepsilon$. The original
reply $r_u(p)$ is $\alpha$, $\beta$, $\mathsf{branch}$ or
$\mathsf{absent}$. Only a reached address has a whole subtree $u|_p$.
Write $u\equiv_h v$ when all replies at $|p|\le h$ agree, including
absence. The same notation applies to finite or infinite ordered trees
with two children at every branch. Let $\Omega$ be the all-branch infinite
tree. No infinite tree is an original source.

Let $\operatorname{ht}(u)$ be maximum leaf depth and $\mu(u)$ minimum leaf
depth, both measured from the original root. A finite tree is isolated
by its inclusive prefix through $\operatorname{ht}(u)$. For any finite-source
set $X$, define $K\in\overline X$ by
$\forall h\ \exists u\in X\ (u\equiv_h K)$. An accumulation point of
$X$ is a prefix limit of a sequence of pairwise distinct members of $X$.
An infinite tree in $\overline X$ is an accumulation point: a finite list
of finite trees cannot approximate it at every depth.

The identities $T_{n+2}=\langle T_{n+1},T_n\rangle$, injectivity of the
atomic index and of $\rho$, and
$\mu(T_n)=\lfloor n/2\rfloor$ are reused from [ABC, Definition 1.3][ABC]
and [NLC, Lemma 3.1][NLC]. Consequently $T_n\to\Omega$ as $n\to\infty$.
The symbol $\rho$ always has (AAB.1)'s interpreted meaning; it is never
a free unary constructor. Repeated occurrences denote the same value.

**Definition 1.2 (entire acquired input).** Fix
$I=(P,R,H_0,H_{\rm rel},Q,N)$ as in [ARH, Definitions 1.1–1.2][ARH].
Both $P,Q$ are finite prefix-free original cuts. A full row $R_A(u)$
consists of its ordered reached holes, its concrete exterior with numbered
holes, and the complete equality partition of their entire subtrees.
An absent cut address contributes no hole. Empty and root cuts are allowed.
The old row $R$ retains its concrete exterior, repeated classes, every
cross-class disequality and every off-task class.

A literal record $(a,p,c)$ requires $r_{\rho^a u}(p)=c$. Each signed
whole-subtree record $e=(a,p,b,q,\bowtie)$ requires

$$
\operatorname{Rel}_e(u)\iff
p\in\operatorname{Pos}(\rho^a u)\ \land\
q\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q,
\qquad \bowtie\in\{=,\ne\}.
\tag{AAB.2}
$$

Both endpoint guards are mandatory for either sign. A negative record is
not the complement of a guarded positive record. All records, including
repetitions, concern one and the same original source within each realization.
The entire domain and its exact row strata are

$$
\begin{aligned}
D&=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\ H_{\rm rel}(u)\},\\
D_r&=\{u\in D:R_Q(u)=r\}.
\end{aligned}
\tag{AAB.3}
$$

**Definition 1.3 (selected joint prefix).** Supply a finite set $B$ of
distinct attained full rows in $R_Q(D)$, with $|B|\ge2$, and choose
$r_*\in B$. Put

$$
J_B(h)\iff
\exists(u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\quad u_r\equiv_h u_s.
\tag{AAB.4}
$$

The tuple has one common original prefix. Its components are different
possible finite original realizations of the same acquired producer
contract. Within each component all records share that source; no single
source is required to carry contradictory row labels. Separate pairwise
witnesses with different prefixes do not satisfy (AAB.4).

Full-row attainment is decidable with finite witnesses by [NSF,
Lemma 5.1 and Theorem 5.2][NSF]; distinctness of the supplied finite labels
is decidable by their three fields. These are input checks. Empty logical
fibers and unattained or duplicate labels do not satisfy Definition 1.3.
Theorems about logical emptiness do not assert an acquired physical entry.

**Assumption 1.4 (supplier domains).** Mathematical supplier statements
are read at the immutable revision
`85caf5d972e524bfd6ea2ce348443b62770f7bff` [SUPPLIER-PIN]. In particular:

- [NIC, Theorems 3.2–3.3 and 4.3][NIC] supplies exact finite mixed covers,
  preserving the same original source in the completeness direction.
- [URR, Corollary 3.2 and its scalar-preserving NSF argument][URR]
  supplies exact existential rank projection. Its fixed residual section
  applies to a Cartesian negative piece and is not an entire image identity.
- [NIC, Proposition 5.3][NIC] supplies finite atomic-navigation cases
  with designated ranks retained. [NSF, Lemma 5.1][NSF] supplies exact
  fixed observation, guard and complete-row compilation.
- [NLC, Theorem 6.1][NLC] decides contact of two exact full-row strata
  at a supplied finite constructor context filled with $\Omega$.
  YES constructs actual finite sources at every requested depth;
  NO identifies a stratum and a finite excluded prefix of that context.
  It imposes no finite-image premise on the other row strata.
- [NPL, Theorem 5.3][NPL] decides the whole full-row image's finiteness
  and enumerates precisely all attained rows in the finite case.

These are ordinary theorem suppliers. Reading their statements or their
related Lean source does not certify this new application in Lean.
Their distinct domains are retained below rather than treating finite
feasibility, a rank-support section, or one contact certificate as a
complete stopping procedure.

## 2. Exact atomic-output representations

**Definition 2.1 (represented anchor).** An anchor representation is a
finite exact whole-source cover

$$
D_{r_*}=\bigcup_b
\{U_b(\mathbf n,\mathbf z):C_b(\mathbf n,\mathbf z)\},
\qquad \mathbf n\in\mathbb N^{k_b},\quad
\mathbf z\in\mathcal T^{m_b}.
\tag{AAB.5}
$$

Its visible whole-source output $U_b$ uses only fixed finite native
grounds, actual pairing and occurrences $T_{n_i+c}$ with fixed
$c\in\mathbb N$. Thus it is independent of every $z_j$. Coordinates
may repeat, occur with different offsets, and obey joint constraints.
No normality or uniqueness of chart choice is assumed.

The predicate $C_b$ is in the exact finite mixed-query language of
Assumption 1.4: a NIC signed pullback has a rank predicate and whole
native disequalities after expansion; Boolean mixed native equalities
and fixed observations can also use the scalar-preserving NSF extension.
Rank predicates are effectively given Presburger formulas. Native powers,
observations, cuts and epochs are fixed finite data. Auxiliary ranks and
residual trees can be jointly constrained; no arbitrary non-Presburger
policy is admitted.

Exactness in (AAB.5) includes two directions: every satisfying tuple
reconstructs an original finite source satisfying all of (AAB.3) and its
full row label; every original member of $D_{r_*}$ is reconstructed as
that same source by some satisfying tuple. This equality is supplied by
NIC's construction, or by a provided exact chart certificate with both
proved directions. A list of sampled atomic sources is insufficient.
An arbitrary proposed chart's unproved surjectivity is not an assumption
silently granted by the class test.

The supplied representation, including its exactness certificate, is
part of the mathematical input. The recognition below decides the
finite-basis condition on this representation. It does not decide whether
an arbitrary fiber has some alternative exact atomic representation,
or whether an arbitrary prose certificate is a correct proof.

**Theorem 2.2 (source-faithful projection).** Let $V_b$ be the indices
of the rank coordinates actually occurring in $U_b$, and write
$\mathbf v=(n_i)_{i\in V_b}$. There is an effectively computed Presburger
predicate

$$
S_b(\mathbf v)\iff
\exists(n_i)_{i\notin V_b}\ \exists\mathbf z\quad
C_b(\mathbf n,\mathbf z)
\tag{AAB.6}
$$

such that the entire anchor fiber, with no source omitted or added, is

$$
D_{r_*}=\bigcup_b\{U_b(\mathbf v):S_b(\mathbf v)\}.
\tag{AAB.7}
$$

A witness for any feasible $\mathbf v$ can recover all eliminated
coordinates and the finite original source.

Proof. On a NIC Cartesian signed piece, NIC Proposition 3.5 applies URR
to the entire native negative pullback. Its rank-support equivalence
is exact for every rank tuple. More generally, URR Corollary 3.2's
scalar-preserving NSF argument leaves designated primitive ranks free
through the finite native branches and existentially eliminates only
the auxiliary scalars. It preserves their actual values in both native
source directions. Conjoin the Presburger policy to the resulting
arithmetic formulas and existentially quantify unused rank coordinates.
Presburger elimination gives (AAB.6). Witness extraction, or finite
enumeration using the guaranteed feasibility, returns finite auxiliary
values. Fixed navigation uses NIC Proposition 5.3's finite rank splits;
it does not replace a variable rank by a finite cutoff.

For one inclusion, a satisfying tuple in (AAB.5) has $S_b(\mathbf v)$
and the same visible output. For the other, (AAB.6) supplies a full
satisfying tuple; $U_b$ does not use any eliminated variable, so that
tuple's original source is precisely $U_b(\mathbf v)$. Its signs, guards,
old classes, exterior and new full label hold by (AAB.5). This proves
(AAB.7). Independence of the output is the essential hypothesis.
Fixing an observable residual tree to URR's section would instead
discard original sources and is not this projection. $\square$

**Definition 2.3 (joint cofinal fibers).** Reindex the used coordinates
of each piece by $\{1,\ldots,k\}$. For a nonempty subset
$A\subseteq\{1,\ldots,k\}$ put $F=\{1,\ldots,k\}\setminus A$ and
define the Presburger set

$$
E_{b,A}=\left\{\mathbf c\in\mathbb N^F:
\forall M\ \exists\mathbf v\quad
S_b(\mathbf v)\ \land\ \mathbf v_F=\mathbf c\ \land\
\bigwedge_{i\in A}v_i\ge M\right\}.
\tag{AAB.8}
$$

An empty coordinate product is the singleton containing the empty tuple.
In particular $E_{b,\{1,\ldots,k\}}$ is either empty or that singleton.
For $k=0$ there are no nonempty $A$. The represented finite-basis class
consists exactly of representations for which every $E_{b,A}$ is finite.
This condition is tested, rather than supplied as a promise or a list
of contacts. No restriction is placed on $D_r$ for $r\ne r_*$.

## 3. Exhaustive synthesis of the anchor boundary

**Theorem 3.1 (decidable eligibility and exact accumulation set).** For
every representation of Definition 2.1, eligibility in Definition 2.3
is decidable. On an eligible representation the complete accumulation
set of $D_{r_*}$ is effectively computed as the finite set

$$
\mathcal K=\{K_{b,A,\mathbf c}:A\ne\varnothing,
\ \mathbf c\in E_{b,A}\},
\tag{AAB.9}
$$

where $K_{b,A,\mathbf c}$ evaluates the actual finite pairing template
$U_b$, replacing every atomic occurrence belonging to coordinate $i\in A$
by $\Omega$ and every other occurrence by its actual finite atom
$T_{c_i+\text{offset}}$. Each point is a finite constructor context with
finite grounds and $\Omega$ fillings. For each listed point and depth $h$,
an actual source in $D_{r_*}$ with that inclusive prefix is computable.
If a cofinal-fiber set is infinite, the anchor has infinitely many
accumulation points; rejection is not a negative answer to $J_B$.

Proof. Formula (AAB.8) is first-order Presburger arithmetic. Finiteness
of a set in $\mathbb N^F$ is equivalent to the sentence

$$
\exists L\ \forall\mathbf c\quad
E_{b,A}(\mathbf c)\Longrightarrow
\bigwedge_{i\in F}c_i\le L.
\tag{AAB.10}
$$

Presburger decision determines this sentence, including when $F$ is
empty. On a finite answer find a bound $L$ by decidable successive bound
queries, then test every tuple in that finite box. The first decision
guarantees this search's termination. This gives all of $E_{b,A}$, not
an undiscovered subset. Only finitely many $b,A$ occur.

For a listed profile, choose for each $t$ a feasible tuple with
$\mathbf v_F=\mathbf c$ and all $v_i\ge t$ for $i\in A$, using (AAB.8).
Every used coordinate has a fixed syntactic atomic occurrence address.
At those addresses the divergent atoms converge to $\Omega$; fixed
atoms and all explicit pair nodes remain unchanged. Hence the resulting
actual sources converge to $K_{b,A,\mathbf c}$. Their output values
are infinitely many: at least one used rank diverges, and its atomic
index is injective. A subsequence of distinct sources witnesses
accumulation. At a requested $h$, taking $v_i\ge2h+2$ for every
divergent coordinate suffices, since all offsets are nonnegative and
$\mu(T_{v_i+c})>h$. Theorem 2.2 lifts the arithmetic witness to the
same original source with all acquired constraints.

Conversely, consider any prefix-convergent sequence of distinct anchor
sources. An infinite subsequence belongs to one piece in (AAB.7).
Choose its used rank tuples. For each of the finitely many coordinates,
extract a subsequence on which it is constant if some value occurs
infinitely often; otherwise extract one on which it tends to infinity.
These successive extractions retain earlier constants and divergence.
If all coordinates were constant, the output template would be constant,
contradicting distinctness. Thus the diverging set $A$ is nonempty.
The fixed coordinates have a tuple $\mathbf c$, and the subsequence
itself proves (AAB.8), with the full joint predicate $S_b$ intact.
Its limit is exactly $K_{b,A,\mathbf c}$. Prefix limits are unique, so
the original accumulation point is in (AAB.9).

For exactness of the finiteness test, within one fixed piece the profile
map $(A,\mathbf c)\mapsto K_{b,A,\mathbf c}$ is injective. At a chosen
syntactic occurrence of any used coordinate, its subtree is either
$\Omega$ or the atom of that coordinate plus its fixed offset. Different
finite ranks give different atoms; a finite atom differs from $\Omega$.
Different profiles therefore differ at some finite reply. In particular
an infinite $E_{b,A}$ gives infinitely many different accumulation points.
A finite union of the finite sets obtained on acceptance has no others,
by exhaustion. Overlap between pieces may give duplicate descriptions
but changes neither conclusion.

Every computed point is infinite. If (AAB.9) is empty, an infinite anchor
fiber would, by the same finite-piece subsequence argument, produce a
nonempty profile, a contradiction. Thus an empty basis means a finite
anchor fiber, not an omitted contact. Ground pieces and empty pieces
are included by the zero-dimensional conventions. $\square$

To compare two descriptions in (AAB.9), expand their finite grounds,
treat $\Omega$ as one distinguished terminal, and recursively replace
$\langle\Omega,\Omega\rangle$ by $\Omega$. Equality of the resulting
finite descriptions decides equality of their completion trees. A
remaining finite leaf distinguishes its tree from $\Omega$; otherwise
ordered pair comparison reduces recursively. Deduplication is optional.
Occurrences of $\Omega$ are mathematical holes, not acquired labels.

**Theorem 3.2 (effective finite remainder after boundary neighborhoods).**
Let an eligible anchor have basis $\mathcal K$. For every choice of
finite depths $e_K$ for $K\in\mathcal K$, the remainder

$$
X=D_{r_*}\setminus
\bigcup_{K\in\mathcal K}\{u:u\equiv_{e_K}K\}
\tag{AAB.11}
$$

is finite and can be enumerated exactly, with original finite sources.
When $\mathcal K$ is empty it is the entire finite anchor.

Proof. An infinite remainder contains distinct sources from one piece.
The coordinate extraction of Theorem 3.1 gives a subsequence converging
to some $K\in\mathcal K$. It eventually agrees with $K$ through $e_K$,
contradicting membership in the remainder. This proves finiteness without
reclassifying a merely sufficient neighborhood list as exhaustive.

For effectiveness translate every finite prefix test in (AAB.11) to
Presburger conditions on the used ranks. At an atom of rank $q$, split
into $q=0$, $q=1$ and $q\ge2$. The first two cases have known leaf
and absent-descendant replies. In the third case a left step gives
$T_{q-1}$ and a right step gives $T_{q-2}$. Following a supplied finite
word takes finitely many such splits, represented with natural affine
auxiliaries when subtraction occurs. Fixed ground and explicit pair
navigation are computed directly. This is exactly NIC Proposition 5.3's
atomic-navigation argument. Every $K$ prefix is computable from its
finite context. Thus each piece's remainder support $S'_b$ is Presburger.

The map from used ranks to $U_b$ is injective: compare any used
coordinate at one fixed syntactic occurrence address and use atomic
index injectivity. Hence the finite output remainder implies each
$S'_b$ is finite. Decide its bounding sentence, find a bound, enumerate
the bounded ranks exactly, and expand $U_b$. Theorem 2.2 guarantees all
listed sources and their original retained predicates. Deduplicate finite
trees by syntactic equality. A piece with no used ranks has at most its
one ground output. All steps terminate. $\square$

## 4. Terminating selected joint-prefix stopping

**Theorem 4.1 (exclusion or actual joint realizers).** On every eligible
represented anchor and input of Definitions 1.2–1.3, there is a terminating
choice between the following mutually exclusive outcomes:

1. A finite $H\ge0$ with $\neg J_B(H)$.
2. An effective procedure which, for every requested $h\ge0$, returns
   actual finite $u_r\in D_r$ for every $r\in B$, all sharing one
   inclusive original $h$-prefix.

Equivalently, with the exhaustively synthesized basis of Theorem 3.1,

$$
\forall h\ J_B(h)
\quad\Longleftrightarrow\quad
\exists K\in\mathcal K\quad
K\in\bigcap_{r\in B}\overline{D_r}.
\tag{AAB.12}
$$

Neither a functional common-output equation presentation nor a contact
list is supplied. All companion fibers remain entire arbitrary signed
full-row strata of (AAB.3).

Proof. Compute $\mathcal K$. For each $K$ choose its finite constructor
context, expanding finite grounds and naming each $\Omega$ occurrence
as a separate hole. Repeated values may fill separate holes; no
disequality between holes is inferred. Apply NLC Theorem 6.1 to each
pair $(r_*,r)$, $r\in B\setminus\{r_*\}$, at this same context.
Theorem 3.1 already proves $K\in\overline{D_{r_*}}$. Therefore YES is
equivalent to $K\in\overline{D_r}$; a NO excluded stratum must be $D_r$,
since no finite prefix of $K$ excludes the anchor. The supplier's finite
queries identify that excluded row with its depth $e_K$.

If some $K$ has YES for every companion, request NLC's realizers at $h$
and keep each companion source. All agree with that same $K$ at $h$.
Obtain an anchor source using Theorem 3.1's joint cofinal arithmetic
witness and Theorem 2.2's lift. The tuple satisfies (AAB.4), with every
sign and guard checked on its own actual finite source. The different
anchor witnesses used internally by the separate pair decisions need
not be identified; replacing them by the one constructed anchor is
valid because every returned companion already matches the same $K$.
No negative constraint is evaluated at the infinite limit.

If no $K$ passes every companion, choose for each $K$ a failed row
$r_K\ne r_*$ and its depth $e_K$. Compute the finite remainder $X$ in
(AAB.11), and set

$$
H=\max\bigl(\{0\}\cup\{e_K:K\in\mathcal K\}
\cup\{\operatorname{ht}(u):u\in X\}\bigr).
\tag{AAB.13}
$$

For any prospective joint tuple, its anchor either matches some $K$
through $e_K$, or lies in $X$. In the first case a companion in $D_{r_K}$
matching the anchor through $H$ would match $K$ through $e_K$, contrary
to exclusion. In the second case agreement with the finite anchor
through $H$ isolates that very tree, forcing a distinct full-row label
on the same source. This is impossible. Thus $\neg J_B(H)$.
With an empty basis, the second case alone applies and (AAB.13)
uses the entire finite anchor. All decisions and enumerations terminate
by the cited supplier, Theorems 3.1–3.2 and Presburger decision.

For completeness of (AAB.12), suppose $J_B(h)$ holds at every depth
and choose its joint tuples at increasing depths. No finite anchor
source can recur at unbounded depths: once the depth reaches its height,
matching would force a different row on that same source. Extract
distinct anchor sources from one piece at depths tending to infinity.
The coordinate extraction in Theorem 3.1 gives a limit
$K\in\mathcal K$. For each fixed $d$, these anchors eventually match
$K$ through $d$, and their companions match the anchor there because
their joint requested depth tends to infinity. Every row therefore has
actual finite $K$-prefix realizers at every $d$. This gives the right
side. Its converse follows from the positive construction above.
Monotonicity of $J_B$ makes the two outcomes exclusive. $\square$

For a piece with $k$ used coordinates, the class test forms $2^k-1$
cofinal-fiber formulas. A basis with $M$ distinct points uses at most
$M(|B|-1)$ NLC pair decisions, plus the finite-remainder calculation in
the negative case. These counts concern these exact supplied domains.
They give no polynomial preparation, running-time, witness-size or
optimal-resource assertion.

## 5. An actually acquired atomic-tail and residual consumer

**Definition 5.1 (same-source mixed history).** Put

$$
W(y)=\langle\rho^2y,\langle\rho y,y\rangle\rangle.
\tag{AAB.14}
$$

Take $P=\{\varepsilon\}$ with its unique reached one-hole full row.
Retain branch literals $(0,\varepsilon,\mathsf{branch})$,
$(0,R,\mathsf{branch})$ and $(0,RR,\mathsf{branch})$. Retain precisely
the signed records

$$
(0,L,2,RR,=),\qquad
(0,RL,1,RR,=),\qquad
(1,RR,0,RR,\ne),
\tag{AAB.15}
$$

each with both reached-endpoint guards. Set $Q=\{L,R\}$ and certified
$N=2$. No additional source-bearing field is inferred from these records.

**Theorem 5.2 (entire fiber, both full rows and actual acquisition).**
The entire source domain of Definition 5.1 is exactly

$$
D=\{W(y):y\in\mathcal T,\ r_y(\varepsilon)=\mathsf{branch}\}.
\tag{AAB.16}
$$

Its full $Q$-row image has exactly two attained labels, both with
reached set $\{L,R\}$ and exterior $\langle\square_1,\square_2\rangle$.
The equal partition's fiber is

$$
D_= =\{\langle T_{n+2},T_{n+2}\rangle:n\ge2\},
\tag{AAB.17}
$$

and the unequal partition's fiber is exactly $W(y)$ for every finite
branch-rooted non-atomic $y$. This input is a successful outcome of
ARH Proposition 2.1's common paid producer, conditional on its complete
handoff premise; its mathematical coordinates are not runtime ports.

Proof. The literals uniquely give $u=\langle x,\langle z,y\rangle\rangle$
with branch-rooted $y$. Original branch positions survive every fixed
iterate, so the two positive records impose exactly $x=\rho^2y$ and
$z=\rho y$ with reached endpoints. Their converse holds on every such
$W(y)$. The negative record is automatic for a finite nonempty $y$:
$\rho^2$ replaces either original leaf by a tree having at least two
leaves, so strictly increases leaf count. If $\rho y=y$, applying
$\rho$ would contradict that increase. Thus both domain inclusions
in (AAB.16) preserve the negative and its guards.

The two entire $Q$-hole values are $\rho^2y$ and
$\langle\rho y,y\rangle$. Reuse the finite-source stability
classification of [SourceTransportCentralizer,
`source_transport_centralizer`, first conjunct][CENTRALIZER], also
stated in ABC's atomic supply: equality holds exactly for $y=T_n$.
Here branch-rootedness gives $n\ge2$, and the atomic recurrence gives
(AAB.17). There are only two partitions of these two reached holes,
and the exterior is fixed, so this lists complete rows rather than
two selected equality bits. The source $y=T_2$ attains the equal row.
The source $y=\langle T_2,T_2\rangle$ attains the unequal row: every
branching atom has two different consecutive atomic children, whereas
these children are equal. No finite branch-rooted non-atom is removed
from the unequal fiber.

Apply ARH Proposition 2.1 to the public literal and endpoint lists in
(AAB.15). The producer actually acquires whole finite endpoints at
their epochs, retains the earlier paid descriptions until comparison,
and makes genuine forward updates to $N=2$. All endpoints here are
reached. Every source in (AAB.16) gives the same specified old row,
literals and signs, and every source giving that retained output is
in (AAB.16) by the proved converse. Its exact post-cut fiber follows
only conditional on ARH Assumption 1.3's complete-state factoring.
The pre-cut traversals and comparisons remain paid and may have no
uniform cost bound over $D$. $\square$

**Theorem 5.3 (exhaustive basis and mixed finite joint witnesses).**
For $B=\{r_=,r_{\ne}\}$, the equal row is an eligible anchor whose
complete accumulation basis is $\{\Omega\}$. For every requested $h$
put $m=2h+2$. The two actual finite sources

$$
u_=W(T_m),\qquad
u_{\ne}=W(\langle T_m,T_m\rangle)
\tag{AAB.18}
$$

belong to their indicated complete fibers and both agree with
$\Omega$ through inclusive depth $h$. Hence $J_B(h)$ holds for every
$h$. For unshared tree syntax their node counts are respectively
$4F_{m+3}-1$ and $8F_{m+3}-1$, with $F_0=0,F_1=1$.

Proof. The anchor chart is $U(n)=\langle T_{n+2},T_{n+2}\rangle$,
$S(n)=(n\ge2)$. Its only nonempty cofinal set is the singleton empty
tuple for $A=\{1\}$. The computed completion is
$\langle\Omega,\Omega\rangle=\Omega$, so Theorem 3.1 proves exhaustion.
In (AAB.18) both arguments of $W$ are branch-rooted and the second
is non-atomic by the distinct-child observation in Theorem 5.2.
Thus the entire acquired predicates and opposite complete rows hold.

Since $\mu(T_m)=h+1$, both these arguments have no leaf at depth
at most $h$. Native $\rho$ preserves original branches and only
expands leaves, so neither fixed iterate creates a shallower leaf.
The explicit pairs in $W$ consequently leave every source address
of depth at most $h$ a branch. Both sources share the one stated
prefix, proving the joint claim. The acquired negative holds on each
finite source although its two compared values coincide in the limit
$\Omega$; finite signed feasibility has not been replaced by a sign
test at that limit.

Atomic leaf counts are $|\operatorname{Leaves}(T_j)|=F_{j+1}$ by
(AAB.1)'s recurrence. For $W(T_m)$ their sum is
$F_{m+3}+F_{m+2}+F_{m+1}=2F_{m+3}$. Pairing two copies of the argument
doubles that sum in the second source. A finite full binary tree with
$l$ leaves has $2l-1$ nodes, giving the stated counts. These are
exact construction sizes of these literal finite witnesses, not read
charges, measured performance or minimum sizes. $\square$

## 6. Conditional paid recovery on the entire acquired source domain

**Assumption 6.1 (original legal service contract).** For service claims
use ARH Assumption 1.3 on the entire $D$, with the same original root,
source and physical register at the authentic certified epoch $N$.
All records were actually acquired and paid before a complete access
cut. The entire accessible initial state is a common recoverable
encoding of $I$ and common parameters, and has exact source fiber $D$.
Every accessible source-bearing cache, count, address, length, program
position, timing field, archive, output, reference, permission and
handle is included. Extra accessible distinctions change the fiber.
Sourcewise finite acquisition does not imply uniformly bounded acquisition.

A controller is deterministic and effective, correct and terminating
for every $u\in D$. Its only new source observations are actual paid
four-valued $\mathsf{Read}(p)$ replies at finite physical words. It may
perform genuine serial forward same-register $\mathsf{ApplyRho}$ and
absorbing $\mathsf{Halt}$. Computation and updates reveal no extra
source-dependent information. No mathematical witness supplies a rank
query, equality oracle, chart selector, reset, reroot, source clone,
original-version access or new observation port. A later entry requires
its own legal contract and payment.

For actual runs keep separate

$$
\begin{aligned}
c_A(u)&=(q_A(u),a_A(u),\ell_A(u)),&
\ell_A(u)&=\sum_{\text{actual reads at }p}|p|,\\
b(A)&=(\sup_Dq_A,\sup_Da_A,\sup_D\ell_A),&
W_\lambda(A)&=\sup_{u\in D}\lambda\cdot c_A(u),
\quad\lambda\in\mathbb Q_{\ge0}^3.
\end{aligned}
\tag{AAB.19}
$$

Every repeated or absent raw read counts; root reads have one call and
zero address length. The same-source weighted sum is taken before its
supremum. Acquisition, local work, strategy preparation, installation,
address generation, transmission, authentication, memory, retention,
output and physical time remain separate costs.

**Theorem 6.2 (selected obstruction and full-image distinction).** A
productive outcome of Theorem 4.1 rules out any uniform finite-new-read
controller for the entire full-row task on $D$ under Assumption 6.1.
A negative outcome for a selected $B$ does not by itself establish
whole-row determination: it excludes only simultaneous representation
of those labels at one prefix.

Proof. A productive tuple includes two different full rows at every
original prefix depth. Therefore no finite depth determines $R_Q$ on
$D$. The exact operational equivalence [ARH, (2.3)][ARH] applies to
this entire signed domain: common complete state, source-totality,
four-valued replies and original-prefix locality are its hypotheses.
The locality supplier includes born and absent physical addresses.
It allows arbitrary finite words and reply-dependent forward updates;
it does not need a rank observation. A uniformly raw-bounded serial
controller would give a finite determining original prefix, contrary
to the witnesses. This proves the obstruction for every allowed
controller. In particular Theorem 5.3 obstructs uniform recovery on
its entire mixed-source domain, not just on the two displayed samples.

For the distinction, let $B$ have three labels. The statement
$\neg J_B(H)$ merely says that no prefix cylinder meets all three
strata. A cylinder meeting two distinct row strata still violates
determination. For two selected labels, their exclusion need not
exclude pairs involving any unselected attained label. Thus full
determination requires all distinct pairs of the whole attained image,
not an inference from a selected multirow negative. $\square$

**Theorem 6.3 (terminating whole-row consumer on the represented class).**
First apply NPL Theorem 5.3 to the entire input. If its whole-row image
is infinite, no uniform finite-new-read controller exists under
Assumption 6.1. If it is finite, let its exact attained row list be
$\mathcal R$. Supply exact atomic-output representations for all but
at most one member of $\mathcal R$, and test their eligibility as in
Theorem 3.1. On acceptance there is a terminating decision of finite
original-prefix determination on the entire $D$:

- If every distinct pair is excluded by Theorem 4.1, the maximum of
  their exclusion depths is a determining depth $H$.
- If some pair is productive, its actual finite sources at every
  requested depth obstruct uniformly raw-bounded whole-row recovery.

For at most one attained row take $H=0$. Empty $D$ has only a vacuous
logical determination conclusion. Failure of an offered cover or of
eligibility rejects this represented class; it is not a recovery NO.

On the determining outcome and $D\ne\varnothing$, at every authentic
permitted $N$ there is a lawful static whole-row service with sufficient
bounds

$$
\begin{aligned}
q_0&=2(2^{H+1}-1),&a_0&=0,\\
\max|p_{\rm physical}|&\le H+\lceil N/2\rceil,&
\ell_0&\le q_0(H+\lceil N/2\rceil).
\end{aligned}
\tag{AAB.20}
$$

Proof. A source-total controller with at most $K$ new reads has at
most $4^K$ terminal outputs: its common deterministic control and
four-valued reply histories give a finite reply tree. This is [NPL,
Lemma 6.1][NPL], and excludes uniform raw bounds for the infinite
whole-row image. In the finite case every pair has an eligible anchor
because at most one row lacks one. Apply Theorem 4.1 to each of the
finitely many pairs. Exclusion depths can be maximized. A pair with
different rows at a prefix of that maximum would contradict its own
exclusion. Conversely a productive pair contradicts every possible
determining depth. This proves the full-domain choice and retains
the complete row image, rather than a finite source sample.

For the positive service reuse ARH's prefix-to-static direction of
(2.3), with [SLH, Theorem 2.2][SLH]'s paid decoder at the actual $N$.
Request all original replies at $|p|\le H$. There are $2^{H+1}-1$
such addresses, each decoded by at most two actual current-register
reads of length at most $H+\lceil N/2\rceil$. No new update or old
version access is used. This proves (AAB.20), counting actual repeated
calls as well.

Enumerate finite native candidate trees and test each against the
complete retained input and the recovered original prefix. Membership
on a finite candidate is decidable by direct evaluation. The actual
source guarantees a successful candidate, so this local computation
terminates sourcewise. Output its full $R_Q$. Determination makes
that row common to all successful candidates and to the actual
source; the chosen candidate is not identified with that source.
Then enter absorbing Halt. Preparation, candidate enumeration and
installation are effective but receive no uniform time, storage or
free-cost guarantee. This is the original legal service interface,
not an additional semantic observation mechanism. $\square$

Irrespective of a uniform obstruction, every finite original source
admits the existing source-total paid static traversal at $N$: decode
its root, and after each decoded branch decode its two original
children. It terminates on that finite tree and uses at most
$2|\operatorname{Pos}(u)|$ new reads, as in [ARH, §31][ARH]. This is
a source-dependent bound, not a uniform bound on an infinite domain.
The sufficient bounds in (AAB.20), the coordinate-worst vector and
the same-source weighted value in (AAB.19) establish no global optimum.
Outputting a row does not erase old records or other accessible fields.
A complete successor retention operation and its exact new source
fiber require a separately supplied, paid original legal contract.

## 7. Correlation, infinite boundaries and the unrestricted gap

**Theorem 7.1 (correlated ranks cannot be replaced by marginals).** Take
the exact atomic piece

$$
U(n_1,n_2)=\langle T_{n_1},\langle T_{n_2},T_{n_1+2}\rangle\rangle,
\qquad S(n_1,n_2)=(n_1\ge2\ \land\ n_2=n_1+1).
\tag{AAB.21}
$$

Its complete accumulation basis is the singleton $\{\Omega\}$.
Replacing $S$ by the Cartesian product of its two rank projections
changes that basis to an infinite set and adds impossible partial
divergence profiles.

Proof. With either coordinate fixed the equality $n_2=n_1+1$ bounds
the other, so $E_{\{1\}}$ and $E_{\{2\}}$ are empty. Both can tend
to infinity jointly, so $E_{\{1,2\}}$ is the singleton empty tuple.
Theorem 3.1 gives exactly the completion with every atomic occurrence
replaced by $\Omega$, which equals $\Omega$. The repeated $n_1$ and
its offset $+2$ are retained at both addresses.

The marginal product is $n_1\ge2,n_2\ge3$. It permits $n_2=c\ge3$
while $n_1\to\infty$, producing
$\langle\Omega,\langle T_c,\Omega\rangle\rangle$ for every such $c$.
These are pairwise distinct accumulation points absent from (AAB.21).
Thus separate rank feasibility and separate unboundedness cannot
supply the joint cofinal condition (AAB.8). $\square$

**Theorem 7.2 (an acquired atomic fiber with an infinite boundary).**
Take the old root row, branch literals at $\varepsilon,L,R$, and
the two guarded records

$$
(1,LL,0,L,=),\qquad (1,RL,0,R,=).
\tag{AAB.22}
$$

At $Q=\{L,R\}$ the unequal full row has the exact source fiber

$$
X=\{\langle T_n,T_m\rangle:n,m\ge2,\ n\ne m\}.
\tag{AAB.23}
$$

It has infinitely many accumulation points and is ineligible as an
anchor in Definition 2.3, although all sources have atomic outputs.

Proof. At a branch-rooted child $t$, the record compares
$(\rho t)|_L$ to $t$. Reuse [ARH, §§4–6][ARH]'s reached branch
certificate classification: this holds exactly for $t=T_j$, $j\ge2$.
Both children and their recorded descendants are reached. The literal
root and both independent child records therefore give exactly
$\langle T_n,T_m\rangle$ with $n,m\ge2$. Its unequal partition adds
precisely $n\ne m$ by atomic injectivity. This proves both source
directions for the entire acquired unequal row, with its fixed exterior
and reached set. ARH Proposition 2.1 supplies the common paid producer
under its handoff premise at $N\ge1$.

For each fixed $c\ge2$, taking $m=c$ and $n\to\infty$, omitting $n=c$,
gives the accumulation point $\langle\Omega,T_c\rangle$. These points
are pairwise distinct. Equivalently $E_{\{1\}}$ contains all $c\ge2$,
so the decidable class test rejects this chosen anchor. The equal row
of the same input does have a finite basis; rejection of the unequal
anchor asserts neither that another anchor fails nor that joint
stopping is impossible. It demonstrates that finite-basis eligibility
is a substantive additional boundary, not automatic atomicity.
$\square$

**Definition 7.3 (ordinary inference and bounded source comparison).**
Theorem 3.1 synthesizes an exhaustive boundary from an exact atomic
source image. Theorem 4.1 connects that boundary to arbitrary companion
full-row fibers and computes the finite remainder needed for a negative
answer. Theorems 5.2–5.3 give one complete actual mixed acquired consumer;
Theorem 6.3 restores the whole-image quantifier for conditional paid
recovery. These are the `repo-derived` additions. Atomic stability,
normal codes, exact mixed covers, rank projection, fixed-depth feasibility,
fixed-context contact, finite row-image decision and paid prefix decoding
are credited supply, not new results of this volume.

The bounded mathematical comparison includes the pinned ARH, ABC, NIC,
URR, NSF, NPL, NLC and [SPC][SPC] interfaces, and the source centralizer
and original-prefix-locality statements. NLC's context is supplied;
its theorem does not synthesize all contacts. SPC's productive signed
certificates are sufficient and its interpreted non-rational examples
show why general contacts cannot all be replaced by finite constructor/
$\Omega$ descriptions. The present theorem does not claim such a
replacement for arbitrary residual-output anchors. No pending extension
is a premise.

The arithmetic facts and comparison results below are `literature-attested`
at the specified primary texts; they are used as intermediate supply or
to delimit transfer, rather than claimed as new theorems of this volume.

- Ginsburg–Spanier, *Semigroups, Presburger formulas, and languages*,
  [Theorems 1.1–1.3][GS], gives Presburger decidability and the
  semilinear correspondence over nonnegative integer tuples.
  Bergsträßer–Ganardi–Lin–Zetzsche, *Ramsey Quantifiers in Linear
  Arithmetics*, [Proposition 3.2 and Theorem 5.1][RAMSEY], states ordinary
  Presburger quantifier elimination and, separately, an existential
  Ramsey-quantifier elimination result. Only ordinary Presburger
  decidability/elimination is used for (AAB.6), (AAB.8) and (AAB.10).
  Its integer formulation restricts to naturals by explicit nonnegativity.
  No Ramsey complexity claim is transferred to native source queries.
- Comon–Lescanne, *Equational Problems and Disunification*,
  [§6.2][CL], explicitly distinguishes its free-term solved forms from
  general equational theories. Treating the native interpreted $\rho$
  as an unconstrained free unary constructor would change the equality
  problem. The native-source bridges used here are NIC/NSF's stated
  bridges, rather than an automatic application of that free-term theory.
- Milius–Moss, *The Category Theoretic Solution of Recursive Program
  Schemes*, [Theorem 7.5 and §7.3, Theorem 7.15][MM], requires guarded
  recursive program schemes and the stated Elgot/completely iterative
  algebra structure; its metric specialization uses contracting
  functors. Such interpreted fixed-point existence or uniqueness does
  not supply all finite signed approximants of arbitrary overlapping
  native equations. No such transfer is a premise of Theorem 4.1.
- Barguñó–Creus–Godoy–Jacquemard–Vacher, *Decidable Classes of Tree
  Automata Mixing Local and Global Constraints Modulo Flat Theories*,
  [Theorem 5.22 and Corollaries 5.23–5.24][FLAT], decides emptiness in
  its specified constrained-automaton classes. Its flat equations have
  the same variables and height at most one. The native distributive
  equation $\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle$
  has height two as an equation over operation symbols. No faithful
  encoding of the entire native signed-closure problem into that class
  is supplied here. Finite emptiness alone is also a different question
  from (AAB.12).

These primary conditions support the arithmetic step and delimit the
other comparison routes. This bounded comparison establishes no
literature-wide absence, priority, originality or undecidability claim.
All proofs remain ordinary mathematics conditional on the named
ordinary supplier statements, without a new Lean, kernel or physical
validation claim.

**Definition 7.4 (unrestricted problem retained as open).** For every
arbitrary complete acquired input and every finite set of distinct
attained full rows, the broader task still asks for a terminating choice
between a finite joint exclusion depth and actual finite common-prefix
representatives at every requested depth. Theorem 4.1 answers that
question exactly on the represented finite-basis class. It does not
establish that arbitrary inputs have an atomic-output anchor, that an
exact eligible chart can always be found, or that arbitrary residual
and nonfunctional overlap has a finite context/$\Omega$ boundary.
Observable residual outputs cannot be existentially projected away.
The concrete missing bridge is a complete effective contact synthesis
or a different terminating alternative for those unrestricted exact
full-source fibers. Failure of this class test supplies no impossibility
theorem for that bridge. Mutual recovery between further relation
expressions requires their own complete source, legal action and paid
retention correspondence. This finite theorem does not settle that
unrestricted programme or any global action/resource optimum.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NLC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_DEPTH_CONTACT.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[CENTRALIZER]: https://github.com/the-omega-institute/trureturing/blob/85caf5d972e524bfd6ea2ce348443b62770f7bff/D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[SUPPLIER-PIN]: https://github.com/the-omega-institute/trureturing/tree/85caf5d972e524bfd6ea2ce348443b62770f7bff
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[RAMSEY]: https://arxiv.org/pdf/2311.04031v1
[CL]: https://perso.ens-lyon.fr/pierre.lescanne/PUBLICATIONS/jsc-diseq.pdf
[MM]: https://arxiv.org/pdf/0904.2385v2
[FLAT]: https://arxiv.org/pdf/1302.6960v2

## 追加锚（本行以下为增补区）
