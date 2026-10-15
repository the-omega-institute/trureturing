# Native cut-birth provenance and literal past-row recovery

## 1. Native sources, complete rows and the chosen origin

**Definition 1.1 (source, update and literal address).** Use the actual finite
nonempty ordered algebra
[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
$\mathrm{Source}=\mathrm{FreeMagma}\ \mathrm{Bool}$, and its native substitution
$\rho$:

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{NBP.1.1}
$$

Native true is alpha and false is beta. Addresses are finite words in $L,R$,
with root $\varepsilon$; native address letters false,true mean $L,R$,
respectively. Write $\operatorname{Pos}(u)$ for actual node occurrences
and $u|_p$ for an existing subtree. Different addresses remain different
occurrences even if their subtrees are equal. The actual
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
readout has four replies $\alpha,\beta,\mathsf{branch},\mathsf{absent}$.
A nonempty continuation at a leaf is absent. Every finite address is
a legal query. No quotient removes brackets, order or leaf labels.

**Definition 1.2 (fixed complete literal row).** Fix a finite prefix-free
public cut $P$, allowing $\varnothing$ and $\{\varepsilon\}$. Reuse
[Sparse Literal History Transport, Definition 59.1](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).
Put $H_P(u)=P\cap\operatorname{Pos}(u)$. Replace each entire subtree at
$p\in H_P(u)$ by an occurrence hole $\square_p$, leaving every exterior
bracket and concrete leaf. Denote that exterior by $C_P(u)$. Retain the
complete partition

$$
p\sim_{\pi_P(u)}q\quad\Longleftrightarrow\quad u|_p=u|_q,
\qquad R_P(u)=(C_P(u),\pi_P(u)).
\tag{NBP.1.2}
$$

Different classes assert disequality. The exterior gives the reached-hole
set and exposes a concrete strict-prefix blocking leaf for every absent
$p\in P$. This is the exact native literal record:
[ActualCutPartitionDecoder](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean),
canonicalRow_record_iff, equates it with canonicalRow. Its reached support,
partition and absence guards are supplied by
[ActualCutPartitionRecovery](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.lean),
canonicalRow_reached, canonicalRow_partition and canonicalRow_absent_guard.

Order holes lexicographically and name a class by the position of its first
hole. These native ordinals need not be consecutive integers. When a partition
is restricted to fewer occurrences, recompute those names. A code for $k$
classes indexes the $k$ occurring names, rather than assuming the raw ordinals
are $0,\ldots,k-1$.

The actual row fiber is the existing legal injective-class-valuation fiber
of Sparse History Theorem 59.4 and
[NativeCutFibers](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean),
legal_values_row and rowFiberEquiv. Its mathematical source witness is
not an input supplied to a row decoder.

**Assumption 1.3 (one actual origin and authenticated updates).** There is one
finite source $u$, one fixed root and the fixed cut $P$. Epoch zero is a
specified origin, which need not be a primitive $\rho$ ancestor. Through
the supplied current epoch $n$, the actual versions are

$$
t_j=\rho^j u,\qquad R_j=R_P(t_j),\qquad H_j=H_P(t_j)
\quad(0\le j\le n).
\tag{NBP.1.3}
$$

The integer $n$ is the authenticated count of genuine serial updates of that
same register. There are no resets, rotations, arbitrary edits, source
substitutions or changing cuts. Origin, version binding and access permissions
are supplied conditions. Authentication certifies continuity; any accessible
source-distinguishing identity is an additional field in the base record
of Definition 6.1.

The static Policy of ActualTreeReadoutAcquisition supplies queries and a
Boolean return, not an update. Serial update semantics are the separately
declared Sparse History §1.3 contract and
[NativeSerialMachine](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean),
Op.applyRho. An inverse computation on finite acquired records is not an
inverse physical action on that register. A mathematical continuation beyond
$n$ describes what pure $\rho$ would produce; it does not certify that
further updates or observations have occurred.

## 2. Inverting the exterior without opening old holes

**Definition 2.1 (occurrence repair and opaque substitution).** Let
$R=(C,\pi)=R_P(\rho v)$ be an actual current row, $H=H_P(\rho v)$ and
$O=H_P(v)\subseteq H$. Restrict $\pi$ to $O$ and canonically rename its
classes. Let $X$ be that set of old class markers.

Prepare a finite term $Q(R,O)$ by visiting the hole occurrences of $C$.
At an old occurrence $p\in O$, retain its restricted class marker $x_{[p]}$.
At a newborn occurrence $p\in H\setminus O$, substitute the literal leaf
$\beta$ if $p$ ends in $L$, and $\alpha$ if it ends in $R$. The root is never
newborn. Retain all other concrete leaves and brackets. This rule acts by
address, even when two current occurrences share one class.

On terms with concrete leaves and markers in $X$, let $\sigma_X$ act as
$\rho$ on concrete leaves, preserve brackets and fix every marker. Its
image is the finite-term grammar

$$
\mathcal I_X::=\beta\mid E\mid x\ (x\in X)
                    \mid\langle\mathcal I_X,\mathcal I_X\rangle.
\tag{NBP.2.1}
$$

Markers are formal atoms distinct from $\alpha,\beta$; assigning an old
hidden value to a marker is neither needed nor allowed in this parsing.

**Theorem 2.2 (exact predecessor-row recovery).** For every finite native
source $v$ and every fixed finite prefix-free cut $P$, there is a finite
partial record decoder $\operatorname{Back}_P$ satisfying

$$
\operatorname{Back}_P\bigl(R_P(\rho v),H_P(v)\bigr)=R_P(v).
\tag{NBP.2.2}
$$

For any two actual sources $v,w$ with the same current row,

$$
R_P(v)=R_P(w)\quad\Longleftrightarrow\quad H_P(v)=H_P(w)
\quad\text{if }R_P(\rho v)=R_P(\rho w).
\tag{NBP.2.3}
$$

Its domain here is actual transition data. Agreement with an arbitrary
alleged row and set is not a certificate of physical provenance.

**Proof.** Reuse
[Transport--Memory Completion, Proposition 22.2, (RA.2205)--(RA.2207)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md):
old addresses persist, their subtrees become $\rho(v|_p)$, and the only
new addresses are the left and right children of an old beta leaf. Those
children have values $\beta,\alpha$, respectively. The same supplier gives
injectivity of $\rho$, exclusion of $\alpha$ from its image and unique
full-image parsing.

Consequently restricting the current partition to old holes gives exactly
the old partition: equality and disequality are both preserved by $\rho$.
Canonical renaming removes any effect of current newborn occurrences on
the old first-occurrence ordinals.

Regard the old row term as having the restricted markers $X$. The key
identity is

$$
Q\bigl(R_P(\rho v),H_P(v)\bigr)=\sigma_X\bigl(R_P(v)\bigr).
\tag{NBP.2.4}
$$

Here the notation on the right means the canonically marked term, with
the partition carried by its repeated markers. Prove the identity by
structural induction on the finite source with stops at old cut addresses.
At a stop, both sides are the same opaque marker. A concrete alpha leaf
maps to beta and has no new children. A concrete beta leaf maps to $E$;
its child is replaced by a hole exactly if that child address is in $P$,
and occurrence repair restores its forced literal value. For a concrete
pair, keep the root bracket and apply the induction to its two sides.

Prefix freedom excludes any further public cut inside an old hole and
excludes a cut strictly below a newly cut child. No address more than one
edge below an old leaf is born in one update. Thus these cases account for
every current cut occurrence, every remaining bracket and leaf, and every
absent-cut guard. They prove the identity for arbitrary source size,
including a stop at the root and no stops.

Extend the supplied image parser to opaque atoms. Set

$$
\delta_X(\beta)=\alpha,\qquad
\delta_X(E)=\beta,\qquad
\delta_X(x)=x,\qquad
\delta_X\langle a,b\rangle
 =\langle\delta_X(a),\delta_X(b)\rangle\quad(a,b\in\mathcal I_X).
\tag{NBP.2.5}
$$

The last rule excludes $E$: its right child $\alpha$ is not in
$\mathcal I_X$. The leaf beta, marker, special block and general-pair
cases are disjoint, and recursion strictly decreases finite term size.
Induction on terms gives $\delta_X\sigma_X=\mathrm{id}$ and induction
on this grammar gives $\sigma_X\delta_X=\mathrm{id}$. Applying $\delta_X$
to (NBP.2.4) recovers precisely the old exterior and restricted partition.
This defines $\operatorname{Back}_P$ on the stated domain using retained
syntax alone. In (NBP.2.3), equal old rows give equal reached sets by
Definition 1.2; equal reached sets and the common current row give equal
old rows by (NBP.2.2). $\square$

**Proposition 2.3 (classwise repair loses an old occurrence).** Take
$P=\{L,RL\}$ and $v=\langle\alpha,\beta\rangle$. The current exterior is

$$
C_P(\rho v)=\langle\square_L,\langle\square_{RL},\alpha\rangle\rangle,
\qquad L\sim_{\pi_P(\rho v)}RL,\qquad O=\{L\}.
\tag{NBP.2.6}
$$

Occurrence repair preserves the old hole although a newborn hole has the
same current value.

**Proof.** The old $L$ subtree alpha maps to beta; the old right beta leaf
expands and its newborn $RL$ also has value beta. With the single old marker
$x$, repair gives $\langle x,E\rangle$, and inverse parsing gives
$\langle x,\beta\rangle=R_P(v)$. Replacing both members of the current
class by beta instead gives the full tree $\langle\alpha,\beta\rangle$
after parsing and removes the old $L$ hole. It is therefore not the
predecessor row. $\square$

## 3. The exact one-step distinction is a feasible current alpha class

**Definition 3.1 (current alpha label).** For a realized current row
$R=R_P(t)$, let $B$ be its class set, with $k=|B|$. Define $A_P(t)\in
B\cup\{\bot\}$ to be the class whose actual hidden value is $\alpha$,
or $\bot$ if no hole has that value. Completeness of the partition makes
this class unique when it exists. This is a semantic label until it has
been acquired or retained.

For a visible node root $q$ of $C$, let $\operatorname{Alpha}_C(q,A)$
hold if it is a concrete alpha leaf, or a hole belonging to class $A$.
A branch root and any other concrete leaf fail this predicate.

**Theorem 3.2 (conditional predecessor, old set and current class).** On
actual transitions $t=\rho v$, conditional on the current complete row
$R$, the three data $R_P(v)$, $O=H_P(v)$ and $A=A_P(t)$ mutually determine
one another. In particular,

$$
O=H\setminus
 \{qd\in H:d\in\{L,R\},\ \operatorname{Alpha}_C(qR,A)\}.
\tag{NBP.3.1}
$$

The root, if cut, remains in $O$. Conversely, $A$ is the current class of
any newborn right hole; it is $\bot$ if there is no such hole.

For any nonempty subset $\mathcal U$ of actual predecessor sources with
common current row $R$, its exact number of predecessor rows is

$$
m(R;\mathcal U)
=\left|\{A_P(\rho v):v\in\mathcal U\}\right|
\le k+1.
\tag{NBP.3.2}
$$

The subsets may impose additional jointly compatible acquired evidence.
No arbitrary subset of $H$ is assumed attainable.

**Proof.** At a reached nonroot cut $p=qd$, prefix freedom ensures that
$q$ is retained as a branch and that the root at $qR$ is visible, possibly
as a hole. No cut can hide a strict ancestor of $p$; another cut can stop
the sibling itself or a descendant but cannot hide that sibling root.

An actual image branch at $q$ is an expanded beta block precisely when
its right child is alpha. If it came from an old branch, its right subtree
would be a $\rho$ image and could not be alpha. A newborn node is a leaf
and cannot be this branch parent. Hence the supplied node-birth criterion
makes $p$ newborn precisely when $\operatorname{Alpha}_C(qR,A)$ holds.
This proves (NBP.3.1).

An old hole has value $\rho(v|_p)\ne\alpha$. A newborn left hole is beta,
and a newborn right hole is alpha. Thus all current alpha holes are
exactly the newborn right cut occurrences; they occupy one class.
The set $O$ therefore recovers $A$ by the stated rule. Theorem 2.2 recovers
the predecessor row from $O$, and the predecessor row gives $O$ from its
hole support. These finite maps prove all equivalences. In each
common-current-row fiber, predecessor row values correspond bijectively
to the attained labels in $B\cup\{\bot\}$, proving (NBP.3.2). For $k=0$
there is one feasible label. $\square$

**Theorem 3.3 (sharp actual $k+1$ family).** For each integer $k\ge1$ there
is a fixed finite prefix-free cut and $k+1$ actual native origins at the
same public current epoch one, with the same current row having $k$
classes and with $k+1$ different predecessor rows. Thus the upper bound
in (NBP.3.2) is sharp. If the complete accessible base retains exactly
the current row and common cut, origin-continuity and epoch conditions,
exact no-new-query predecessor recovery requires $k+1$ supplementary
configurations, or $\lceil\log_2(k+1)\rceil$ fixed-width bits.

**Proof.** Choose any finite ordered full binary skeleton with $k$ leaf
sites $r_1,\ldots,r_k$ and set $P=\{r_iR:1\le i\le k\}$. Such skeletons
exist by successively replacing a leaf by a pair; their leaf sites are
prefix-free, and appending $R$ preserves that property. Reuse the native
orbit $T_i=\rho^i\alpha$ from
[Fibonacci Atomic Relation Generation, Theorem 3.2](FIBONACCI_ATOMIC_RELATION_GENERATION.md).
The $T_i$ are pairwise different: cancelling a common iterate by
injectivity would otherwise put alpha in a positive $\rho$ image.

For $a=0,\ldots,k$, fill site $i$ by

$$
s_i^{(a)}=
\begin{cases}
\beta,&a=i>0,\\
\langle\alpha,T_i\rangle,&\text{otherwise},
\end{cases}
\qquad u_a=\text{the skeleton filled by }(s_i^{(a)})_{i=1}^k.
\tag{NBP.3.3}
$$

After one update each retained site has exterior
$\langle\beta,\square_{r_iR}\rangle$. Its hidden right value is alpha
at the selected site and $T_{i+1}$ elsewhere. These $k$ values are
pairwise distinct in every source. All current complete rows are
therefore identical with $k$ singleton classes. Their old reached sets
are $P$ for $a=0$ and $P\setminus\{r_aR\}$ for $a>0$. Theorem 2.2 gives
$k+1$ distinct predecessor rows, while Theorem 3.2 excludes any further
predecessor row in this current-row fiber. The ordinary finite
identification argument, reused in Theorem 6.2, gives the stated bits.
For $k\ge2$, different selected sites also show that merely retaining
the number of newborn holes is insufficient. $\square$

**Mathematical citation 3.4 (direction of the marker).** The
[Native Alpha Recut Memory companion, Theorems 2.1--3.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
already classifies forward old/new collisions and the needed alpha
marker on the **old** row: a newborn left beta can collide with an old
alpha value after that value is updated. Theorems 2.2--3.3 here concern
the **current** class with value alpha and reconstruct the previous row.
The forward conditional marker can discard its alpha distinction when
no future left birth needs it; it is not the full current label of
Definition 3.1. The two tasks have different fibers and directions.
Neither their identical $k+1$ upper-bound form nor a forward recurrence
supplies the predecessor correspondence (NBP.2.4).

## 4. Finite past histories and the two birth records

**Definition 4.1 (predicted births and causal table).** Reuse
[Transport--Memory Completion, Lemma 23.2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md).
Relative to the chosen origin $u$, every finite address has the finite
semantic birth time

$$
b_u(p)=\min\{j\ge0:p\in\operatorname{Pos}(\rho^j u)\},
\qquad p\in\operatorname{Pos}(\rho^j u)\Longleftrightarrow b_u(p)\le j.
\tag{NBP.4.1}
$$

The full cut vector is $b_P(u)=(b_u(p))_{p\in P}$. At authenticated $n$,
define its causal first-appearance table

$$
B_n^u(p)=
\begin{cases}
b_u(p),&b_u(p)\le n,\\
\ast,&b_u(p)>n.
\end{cases}
\tag{NBP.4.2}
$$

The star records no appearance in the executed prefix. A numeric zero
records initial presence, not a pre-origin construction event. Positive
entries concern first existence under the actual update prefix, provided
the source/epoch conditions hold. They do not record the first time an
observer happened to read the address. An entry of the full vector greater
than $n$ is a prediction about continued pure $\rho$.

**Theorem 4.2 (completing predictions from the acquired exterior).** An
actually acquired origin row $R_0$ determines the full $b_P(u)$ by finite
computation without another source query. More generally, $(R_n,B_n^u)$
determines every still-future entry directly from $R_n$. If $p$ is
unreached at epoch $n$, let $f$ be its unique visible concrete blocking
leaf, write $p=fs$ with $s\ne\varepsilon$, and set
$\eta(\alpha)=0,\eta(\beta)=1$ and $w(s)=\#_L(s)+2\#_R(s)$. Then

$$
b_u(p)=n+2-\eta(t_n|_f)+w(s^-),
\tag{NBP.4.3}
$$

where $s^-$ deletes the last edge. Numeric entries of $B_n^u$ are kept
unchanged. At $n=0$, reached cuts have birth zero and this formula gives
all remaining entries.

**Proof.** The absence guard supplier of Definition 1.2 exposes $f$;
prefix freedom prevents an opaque hole from covering its path. The first
leaf encountered on that path is unique. Since $p$ is still absent,
monotonicity of positions shows that it has never appeared before $n$.
Apply the existing leaf-sector formula
[Transport--Memory Completion, Proposition 24.1, (RA.2403)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)
to the concrete leaf of the current seed $t_n$. The number of further
updates to its nonempty suffix $s$ is exactly
$2-\eta(t_n|_f)+w(s^-)$. Adding the already executed $n$ proves (NBP.4.3).
The computation reads only retained leaf labels and address letters,
not the hidden class values. It predicts continuation; it does not
acquire an event at the predicted time. $\square$

**Theorem 4.3 (fixed-epoch mutual recovery).** For fixed public $P$ and
known authenticated $n$, on actual histories satisfying Assumption 1.3
there are effective inverse recoveries between the three realized
record images

$$
(R_0,\ldots,R_n)
\ \longleftrightarrow\ (R_n,B_n^u)
\ \longleftrightarrow\ (R_n,b_P(u)).
\tag{NBP.4.4}
$$

Thus clipping a full vector to its causal table is injective conditional
on the current row in an actual fixed-epoch fiber, including before
saturation. These are recoveries of mathematical row values and birth indices.

**Proof.** The finite row history gives $R_n$ and the first index at which
each cut occurs, or star if it never occurs. Conversely its causal table
gives every earlier reached set

$$
H_j=\{p\in P:B_n^u(p)\ne\ast,\ B_n^u(p)\le j\}
\quad(0\le j\le n).
\tag{NBP.4.5}
$$

Starting with $R_n$, apply $\operatorname{Back}_P(R_j,H_{j-1})$ for
$j=n,n-1,\ldots,1$. Each application has actual transition data by
induction, so Theorem 2.2 returns $R_{j-1}$. At $n=0$ nothing is inverted.
The resulting history gives $R_0$, which computes the full vector by
Theorem 4.2. Equivalently, that theorem completes each star directly from
$R_n$. The full vector clips to $B_n^u$ by (NBP.4.2). All compositions
return the original records on their realized images, and all calculations
are finite. No old hidden subtree is reconstructed or queried. $\square$

**Proposition 4.4 (unpaired predictions and lack of forward partition
closure).** The following nonrecoveries occur on native sources.

At $P=\{L,R\}$ and $n=0$, alpha and beta both have causal table
$(\ast,\ast)$, but full vectors $(2,2)$ and $(1,1)$. The causal table
alone therefore need not recover full predictions. Full predictions
alone need not recover rows: $\langle\alpha,\alpha\rangle$ and
$\langle\alpha,\beta\rangle$ both have vector $(0,0)$ but different
origin partitions.

Even an origin row together with its full cut vector need not determine
the next complete row. Reuse the actual source pair in
[Sparse History Proposition 65.3, (SLH.65.2)](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md):
at $P=\{LL,R\}$, $x=\langle\beta,\alpha\rangle$ and
$y=\langle\beta,\beta\rangle$ have the same origin row and full vector
$(1,0)$, yet $R_P(\rho x)\ne R_P(\rho y)$.

**Proof.** The atomic birth times follow from the supplied leaf-sector
formula. In the two already-branched origin sources every cut is present
at zero, while their two hole values are equal in the first and unequal
in the second. For the last pair, the initial exterior is
$\langle\beta,\square_R\rangle$, with $LL$ blocked. After one update,
$LL$ is a newborn beta. The current $R$ value is beta for $x$ and $E$
for $y$, so the current $LL,R$ classes agree only for $x$. This reuses
the existing forward obstruction and adds its equal birth vectors.
Birth predictions determine reachability, whereas forward partition
closure requires the separately owned old-alpha distinction. $\square$

## 5. The actual birth family and its closed-prefix correspondence

**Definition 5.1 (actual jointly attained family).** Put

$$
\mathcal B(P)=\{b_P(u):u\in\mathcal T\},\qquad K_P=|\mathcal B(P)|,
\qquad P_L=\{s:Ls\in P\},\quad P_R=\{s:Rs\in P\}.
\tag{NBP.5.1}
$$

For two suffix vectors, $a\boxtimes c$ means reattach their coordinates
by $L,R$ to form one vector on $P$. These families concern one whole
actual source per vector; they are not products of coordinatewise birth ranges.

**Theorem 5.2 (effective actual-family recursion).** The empty cut has
$\mathcal B(\varnothing)=\{()\}$ and the root cut has
$\mathcal B(\{\varepsilon\})=\{(0)\}$. For every nonempty prefix-free cut
not containing the root, define

$$
v_\alpha(p)=2+w(p^-),\qquad v_\beta(p)=1+w(p^-).
$$

Then its exact recursion is the deduplicated set union

$$
\mathcal B(P)=
\{v_\alpha,v_\beta\}\ \cup\
\{a\boxtimes c:a\in\mathcal B(P_L),\ c\in\mathcal B(P_R)\}.
\tag{NBP.5.2}
$$

It effectively computes a finite family of actual vectors.

**Proof.** A source root is alpha, beta or a pair. For an atomic root
the leaf-sector formula gives the two displayed vectors. If
$u=\langle s,t\rangle$, its child roots are present at origin zero and

$$
b_u(Lq)=b_s(q),\qquad b_u(Rq)=b_t(q).
\tag{NBP.5.3}
$$

No time shift is added. Conversely, actual witnesses $s,t$ for any two
suffix vectors give their joint witness $\langle s,t\rangle$, so every
joined vector is attained. An empty suffix cut carries no coordinate
and has its one empty vector. The cases exhaust all native sources.

Suffix cuts reduce the maximum nonzero address length. Induction on that
length with the two base cases therefore proves finiteness and gives a
terminating finite set construction using integer-vector equality for
deduplication. Every entry in the construction has the actual witness
just described. This neither selects nor acquires an unknown source.

Cardinal addition would be false in general. At $P=\{LL\}$ the atomic
beta vector is $(2)$, and the pair source $\langle\alpha,\alpha\rangle$
has that same vector. In fact the family is $\{(0),(1),(2),(3)\}$:
the pair alternatives give $0,1,2$, and the atomic alpha gives $3$.
Thus $K_P=4$, whereas $K_{P_L}K_{P_R}+2=3\cdot1+2=5$. $\square$

**Theorem 5.3 (complete-level births are exactly the existing closed
prefixes).** Let $P_d=\{L,R\}^d$ be the complete depth-$d$ cut. For
$d\ge1$ and any actual sources $u,v$,

$$
b_{P_d}(u)=b_{P_d}(v)
\quad\Longleftrightarrow\quad
\operatorname{Pref}_{d-1}(u)=\operatorname{Pref}_{d-1}(v),
\tag{NBP.5.4}
$$

where $\operatorname{Pref}_r$ retains all four literal replies through
depth $r$, including boundary branch labels and absence below leaves.
The induced effective bijection is

$$
\mathcal B(P_d)\ \simeq\ \mathcal V_{d-1},
\tag{NBP.5.5}
$$

with the actual closed-prefix family $\mathcal V_r$ already constructed
in Sparse History Theorem 3.2 and counted in Mathematical Citation 11.3.

**Proof.** In a length-$d$ vector the coordinate $R^d$ distinguishes the
three possible origin root constructors. Atomic alpha and beta have
respective values $2d$ and $2d-1$. A paired origin has at that coordinate
the right subtree's birth for $R^{d-1}$, which is at most $2d-2$ by the
existing reachability bound. Thus the atomic vectors are separate from
each other and from every paired vector.

At $d=1$ the three vectors are $(2,2),(1,1),(0,0)$, exactly the three
depth-zero prefixes alpha, beta and branch. For $d>1$, identify an
atomic root by the distinguished coordinate and recover its entire
prefix, including absence at descendants. In the paired case, split
the vector into its left and right blocks. Apply induction to recover
the two complete depth-$(d-2)$ child prefixes, and join them under a
branch root. This recovers the depth-$(d-1)$ prefix. Conversely an
atomic prefix determines its formula vector; a branch prefix determines
both child blocks by induction and hence their joined vector. Every
existing $\mathcal V_{d-1}$ prefix has a finite native source realization
by the cited supplier. The two maps are therefore inverse on actual
families, establishing the bijection. $\square$

The numerical count is a consequence of this correspondence, using the
already owned recurrence, not a new closed-prefix counting result.
Sparse History (SLH.11.4) supplies

$$
v_0=3,\qquad v_r=2+v_{r-1}^2,\qquad v_r=|\mathcal V_r|.
$$

Consequently $K_{P_0}=1$, $K_{P_d}=v_{d-1}$ for $d\ge1$, and the same
counts, reindexed, satisfy

$$
K_{P_d}=K_{P_{d-1}}^2+2\quad(d\ge1),\qquad
K_{P_1}=3,\quad K_{P_2}=11,\quad K_{P_3}=123.
\tag{NBP.5.6}
$$

The substantive transfer is (NBP.5.4): complete-level birth provenance
preserves exactly this existing complete-prefix distinction.

**Theorem 5.4 (effective uniform supplementary code).** Let
$D=\max(\{0\}\cup\{|p|:p\in P\})$ and put

$$
T_\varepsilon=0,\qquad T_p=2+w(p^-)\quad(p\ne\varepsilon).
\tag{NBP.5.7}
$$

The attained family satisfies

$$
K_P\le\prod_{p\in P}(T_p+1)\le(2D+1)^{|P|}.
\tag{NBP.5.8}
$$

Conditional on public $P,n$ and the current row, an already available
full birth vector or an already available causal table has an effective
fixed-width supplementary encoding of at most
$\lceil\log_2 K_P\rceil$ bits. For complete levels,
$K_{P_d}<2^{2^d}$, so at most $|P_d|$ supplementary bits suffice.

**Proof.** A reached origin cut has birth zero. Otherwise its first blocking
origin leaf has address $f$ and $p=fs$ with $s$ nonempty. The existing formula
gives $b_u(p)=2-\eta(u|_f)+w(s^-)$. Since $p^-=fs^-$, this is at most
$2+w(p^-)=T_p$. The root has birth zero, and $w(p^-)\le2(|p|-1)$ gives
$T_p\le2D$. Every actual vector thus lies in the finite box of (NBP.5.8).
The box is only an upper bound; (NBP.5.2) is the actual family.

Construct that family by Theorem 5.2 and sort its vectors in public
coordinate order. An acquired vector is encoded by its index. For
causal tables at the known $n$, instead sort and deduplicate

$$
\{(b(p)\text{ if }b(p)\le n\text{ else }\ast)_{p\in P}:
       b\in\mathcal B(P)\}.
\tag{NBP.5.9}
$$

Its size is at most $K_P$. Encoding and decoding compare finite retained
records with this finite dictionary and terminate. They do not test
unknown hidden values or solve conditional source feasibility. Theorem 4.3
then decodes the history. This is the existing finite indexing/counting
argument applied to the identified native family.

For complete levels, start with $K_{P_0}=1<2$ and use the reused
recurrence. If $K_{P_{d-1}}\le Q-1$ with $Q=2^{2^{d-1}}\ge2$, then
$K_{P_d}\le(Q-1)^2+2<Q^2=2^{2^d}$. Integer induction proves the bound,
and taking the ceiling of the binary logarithm gives at most $2^d$
bits. The root cut actually needs zero birth bits.

The code width counts the supplement only. The finite dictionary,
its construction, public cut addresses, current row, epoch,
authentication, workspace, output and acquisition are outside this
quantity and remain separate resources. $\square$

## 6. Exact ambiguity after all accessible base data are included

**Definition 6.1 (complete conditional fiber).** Fix public $P,n$ and an
attained base record $z$ before adding the proposed supplement. It
determines $R_n$. Let $\mathcal U_z\ne\varnothing$ consist of origins
jointly compatible with every field of $z$ under the same-source
contract. Compatibility includes every accessible acquired history,
source-dependent identifier, timing, allocation length, program/control
field, pointer, permission-dependent view, cached value, output and
queryable archive. If several actual executions are possible, an origin
belongs to $\mathcal U_z$ when one such execution realizes the complete
$z$; different schedules are not silently identified as raw histories.

No effective membership oracle for $\mathcal U_z$ is assumed. Define

$$
M_{P,n}(z)=|\{B_n^u:u\in\mathcal U_z\}|.
\tag{NBP.6.1}
$$

A supplement is a finite configuration selected from the already acquired
information, with a deterministic decoder using $z$ and that configuration
and making no new source queries.

**Theorem 6.2 (exact conditional history ambiguity).** For every such
attained base record,

$$
\begin{aligned}
M_{P,n}(z)
&=|\{(R_0^u,\ldots,R_n^u):u\in\mathcal U_z\}|\\
&=|\{b_P(u):u\in\mathcal U_z\}|
\le K_P.
\end{aligned}
\tag{NBP.6.2}
$$

Any exact supplementary representation for the whole finite past needs
at least $M_{P,n}(z)$ distinct configurations, hence at least
$\lceil\log_2 M_{P,n}(z)\rceil$ fixed-width bits. As a conditional
information count, that minimum is attained by labeling the distinct
history values. This does not supply an effective optimal encoder for
an arbitrary $z$ or an oracle for its actual feasible origins.

**Proof.** All origins in $\mathcal U_z$ have the same $R_n$ and epoch.
Theorem 4.3 gives bijections between the displayed attained record values
even after joint restriction by $z$. This proves the two equalities;
actual-family inclusion gives the upper bound.

Two different histories in this fiber cannot receive one supplementary
configuration: the decoder would have the same complete $z$, the same
configuration and no new source response, and would return one history
for both. Thus the history alternatives inject into its configuration
alphabet. Conversely, assigning one label to each distinct history and
mapping it back realizes that finite information count. Determining
the optimal feasible label set from arbitrary accessible constraints
is an additional algorithmic problem; it is not part of this inverse
correspondence. The public actual-family code of Theorem 5.4 supplies
an effective upper bound when the vector or table has been acquired.

This reuses the generic injective identification/cardinality argument of
[FiniteIdentificationCapacityBound](../../../D5/S3/ConceptDynamics/Experiment/FiniteIdentificationCapacityBound.lean),
finite_identification_capacity_bound and cost_form, and the ordinary
finite-answer counting in Sparse History §§8.2 and 14.3. The native
addition is identifying exactly which attained histories those
configurations must distinguish. $\square$

**Theorem 6.3 (sharp depth-one history fiber).** At $P=\{L,R\}$ and public
epoch $n=2$, let $D_{\ne}$ be the two-hole exterior with two distinct
classes. If the base data consist exactly of that current row and the
common source/epoch conditions, then

$$
M_{P,2}(D_{\ne})=K_P=3.
\tag{NBP.6.3}
$$

Three supplementary configurations, or two fixed-width bits, are
necessary and sufficient.

**Proof.** The actual origins alpha, beta and $\langle\alpha,\beta\rangle$
give respectively

$$
\begin{array}{c|c|c}
u& (R_0,R_1,R_2)&b_P(u)\\ \hline
\alpha&(\alpha,\beta,D_{\ne})&(2,2)\\
\beta&(\beta,D_{\ne},D_{\ne})&(1,1)\\
\langle\alpha,\beta\rangle&(D_{\ne},D_{\ne},D_{\ne})&(0,0).
\end{array}
\tag{NBP.6.4}
$$

In the second origin, the epoch-two hole values are $E,\beta$; in the
third they are $E,\rho^2\beta$, and in the first they are $\beta,\alpha$.
Each pair is unequal. The three current complete rows coincide, while
the three histories differ. Theorem 5.3 and the existing depth-zero
prefix count give exactly three actual cut vectors, excluding a fourth
history in this fiber. Theorem 6.2 proves the exact count and bits.

At epoch zero, by contrast, retaining $R_0$ already determines $b_P$,
so this additional conditional information count is one. Information
needed after discarding earlier rows must not be charged a second time
while those rows or their readable archives remain in the base. $\square$

## 7. Saturation, edge cuts and concrete nonrecoveries

**Theorem 7.1 (sharp saturation and the predecessor off-by-one).** Put

$$
\tau_P(u)=\max(\{0\}\cup\{b_u(p):p\in P\}),\qquad
T_P=\max(\{0\}\cup\{T_p:p\in P\}).
\tag{NBP.7.1}
$$

Then $\tau_P(u)\le T_P\le2D$, and $T_P$ is the exact worst-source time
at which all cut addresses have appeared. Source alpha attains every
coordinate maximum simultaneously. On a step whose predecessor epoch
$j$ is already saturated, $\operatorname{Back}_P(R_{j+1},P)$ needs no
extra old-set record. Uniformly over origins, this guarantee applies
at current epochs $n\ge T_P+1$, not merely at $n=T_P$.

**Proof.** Theorem 5.4 gives the upper bound; the atomic formula for alpha
is $b_\alpha(p)=T_p$ for nonroot $p$, with root birth zero. This proves
worst-source attainment, also for empty/root cuts. Monotonicity yields
$H_j=P$ exactly when $j\ge\tau_P(u)$. Hence Theorem 2.2 can use the
known old set $P$ on the next step. Its uniform current-epoch condition
is $n-1\ge T_P$.

Current saturation alone cannot justify $O=P$. At $P=\{L,R\}$ and
$n=2=T_P$, the origins alpha and beta in (NBP.6.4) have the same
saturated current row. Their predecessor rows are beta and $D_{\ne}$,
and their previous reached sets are $\varnothing$ and $P$. Even after
all later steps are individually mask-free, the early three histories
in Theorem 6.3 remain different and require their early provenance.
$\square$

**Proposition 7.2 (empty, root and noncovering cuts).** With $P=\varnothing$,
every row is the full source tree and the birth vector is empty; existing
full-image parsing recovers predecessors and, at known $n$, the entire
finite past with zero birth supplement. With $P=\{\varepsilon\}$,
every row is one hole with one class, its birth is zero, and at known
$n$ its finite row history is the constant sequence. This root row
does not determine the hidden source.

A finite noncovering cut can have bounded birth supplementary width
while its literal exterior grows without bound.

**Proof.** The two edge cuts follow directly from Definition 1.2 and the
supplied inverse parser. For the last assertion take $P=\{L\}$ and
$u=\langle\alpha,\alpha\rangle$. At every epoch the row exterior is
$\langle\square_L,T_n\rangle$. The existing recurrence
$T_{n+2}=\langle T_{n+1},T_n\rangle$ gives unbounded tree size. Its
only cut was present at zero, so its birth vector is the constant $(0)$.
Finite supplementary information does not bound the retained concrete
row. $\square$

**Proposition 7.3 (unknown epoch and late row-only entry).** Neither
current row plus full births nor current row alone generally restores
a missing elapsed epoch or omitted origin provenance.

**Proof.** Fix origin alpha and $P=\{L,R\}$. At epochs two and three the
current row is $D_{\ne}$ and the full vector is $(2,2)$ in both. The
predecessor is beta at epoch two and $D_{\ne}$ at epoch three; the complete
finite histories also have different lengths. Thus the inputs without
$n$ do not determine either target.

Even with known $n=2$, alpha and beta in (NBP.6.4) give the same current
row but different full vectors and histories. A late row-only observer
cannot manufacture the missing early table. Applying Theorem 4.2 to
that late row as a new seed predicts births relative to the new seed;
it gives zero for all already reached cuts and does not recover their
first dates relative to the old origin.

The intrinsic coordinate law
[IntrinsicSubstitutionCoordinates](../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean),
all_source_coordinate_law, increases maximal inverse depth by $n$ from
the origin's own depth. Since that origin need not be primitive,
intrinsic depth is not the authenticated elapsed epoch used here. $\square$

**Proposition 7.4 (hidden sources, changing cuts and raw events).** All
same-cut row values and all cut births together need not recover the
origin source, an arbitrary changed-cut row, or raw event history.

**Proof.** At $P=\{L,R\}$ take $u=\langle\alpha,\beta\rangle$ and
$v=\langle\beta,\alpha\rangle$. Both have births $(0,0)$ and row
$D_{\ne}$ at every epoch: iterated injectivity preserves the inequality
of their child values. Yet their origin raw $L$ replies are alpha and
beta, respectively. At the changed cut $Q=\{L\}$ their origin exteriors
$\langle\square_L,\beta\rangle$ and $\langle\square_L,\alpha\rangle$
differ. Thus even the full same-cut past-and-future row sequence does
not recover these targets.

For event history, consider this same source contract with no extra
update: one finite schedule reads the root once, and another reads it
twice before handing off the same semantic row and birth data. They
have different actual read counts and ordered event words but identical
source versions, row values and births. The tables say when addresses
exist, not which reads, pauses, comparisons or handoffs occurred.
Physical elapsed time is also not an update count. $\square$

## 8. Lawful provenance acquisition and the scope of the supplement

**Assumption 8.1 (acquired inputs and complete handoff).** The complete row
is supplied by lawful acquisition on a stationary version of the one actual
source. Equality in its partition is computed on actually acquired finite
subtrees, as in Sparse History Definition 59.2, rather than through an
unknown-subtree equality port.

For one-step recovery, a possessor of the predecessor row can retain its
reached set before that row is lost and deliver it with the actual current
row. For whole-past recovery, either of two acquisitions is supplied:

- A possessor of the acquired origin row computes the full vector by
  Theorem 4.2 before losing that row and retains its code.
- A same-source observer starts with acquired $H_0$ and, through
  consecutive authenticated epochs, acquires each reached set and
  retains its first-appearance table. An epoch's current complete row
  is also lawfully acquired when it is used for recovery.

The first route can be owned by the existing origin-row producer or by a
consumer that already possesses that row. It does not require another
full-source acquisition merely to compute births. The second route requires
enough acquisition to establish first appearances, including initial
presence. First-observed dates from skipped sampling do not supply this
exact table without additional evidence.

The current row, the chosen supplement and public conditions are handed
to a legally continuing consumer. Its complete accessible base is
Definition 6.1; if intended to contain only the declared row and common
fields, it satisfies the value-forgetting condition of Sparse History
Assumption 59.3. No discarded tree, old output, trace, readable pointer,
source-specific length or timing supplies an uncounted distinction.
Old physical archives may remain inaccessible; their exclusion from
this information fiber does not assert physical erasure.

**Theorem 8.2 (finite recovery on supplied records, with paid acquisition).**
Under Assumptions 1.3 and 8.1, the corresponding predecessor or finite
past-row recovery uses zero fresh native source queries after its inputs
are acquired. The uniform code bound and exact conditional counts are
supplementary information bounds, not total resource bounds.

**Proof.** Theorem 2.2 visits the acquired finite row, repairs occurrences,
restricts its acquired partition and parses finite syntax. Theorems 4.2
and 4.3 use retained addresses, leaf labels, epochs and table entries.
Theorem 5.4 uses a finite public actual-family dictionary. None of these
maps requests a hidden value or a fresh readout response.

Initial paid full-source acquisition can be supplied by
[NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean),
native_source_producer: its actual fixed traversal reads each real node
once and builds the acquired source from those replies. That supplier
retains its full native production trace; it does not by itself realize
the narrower complete handoff of Assumption 8.1. Its unknown-source proof
parameters, and NativeCutFibers.recover's source witness, do not become
services available to the consumer.

Acquisition of later complete partitions, authentic update execution,
origin/version binding, permissions and any new entry after absorbing
stop remain supplied and paid. Birth retention is not an autonomous
forward partition updater, by Proposition 4.4. Symbolic inverse parsing
does not physically reverse $\rho$.

Current-row and public-address storage, the public epoch, authentication
records, installed programs and dictionaries, temporary reconstruction
storage, history outputs, source/register storage, old archives and their
acquisition costs are not included in $\lceil\log_2 K_P\rceil$ or
$\lceil\log_2 M_{P,n}(z)\rceil$. In particular the epoch has unbounded
integer width, an output can contain $n+1$ rows, and a noncovering exterior
can grow as in Proposition 7.2. The causal table has at most $|P|$ first
appearances, but there may be arbitrarily many subsequent updates and reads.
Zero fresh queries in this decoding step therefore yields no free
acquisition, fixed peak storage, fixed total work or lifetime address-cost
bound. $\square$

**Mathematical citation 8.3 (ownership, ordinary deduction and literature).**
The native source, row, legal-fiber, acquisition and serial-operation
suppliers are cited in §§1 and 8. The actual node decomposition, subtree
transport, injectivity and image parser belong to Transport--Memory
Completion §22; eventual births and leaf-sector arithmetic belong to
its §§23--24. Original-hole transport in Sparse History §60 preserves
original holes and is distinct from recovering the current same-cut
predecessor. The forward alpha collision and closure theory belongs to
Native Alpha Recut Memory. Sparse History Theorem 3.2 and Mathematical
Citation 11.3 already own the complete-prefix family and its count
recurrence; its generic answer counting and the identification-capacity
supplier own the cardinal-to-bit step.

The repo-derived ordinary addition is the opaque-row identity (NBP.2.4),
its exact attained predecessor/current-alpha correspondence and sharp
native family, the fixed-epoch record equivalence (NBP.4.4), and the
precise birth-vector/closed-prefix correspondence (NBP.5.4). The actual-family
recursion and conditional history bounds apply those correspondences on
the joint native source domain. These are ordinary mathematical proofs,
not Lean kernel certification or a worldwide originality claim.

The literature-attested antecedents delimit the transfer:

- [C. H. Bennett, “Logical Reversibility of Computation”, IBM Journal of
  Research and Development 17 (1973), 525--532](https://www.dna.caltech.edu/courses/cs191/paperscs191/bennett1973.pdf),
  pp. 525--526, describes predecessor ambiguity caused by discarded
  information and retention of computation history. It supplies that
  general motivation, not the native opaque-hole inverse, its minimal
  conditional alternatives, or a permitted physical inverse action.
- [J. R. Driscoll, N. Sarnak, D. D. Sleator and R. E. Tarjan, “Making Data
  Structures Persistent”, Journal of Computer and System Sciences 38
  (1989), 86--124](https://www.cs.cmu.edu/~sleator/papers/another-persistence.pdf),
  pp. 86--89, defines access to old versions and counts elementary
  linked-structure access/update steps. Accessible retained versions
  are a different paid sufficient input. A global $\rho$ can comprise
  many elementary updates; that paper's update bounds do not assign
  constant cost to one global substitution.
- [J. C. Reynolds, “Separation Logic: A Logic for Shared Mutable Data
  Structures”, LICS (2002), 55--74](https://www.cs.cmu.edu/~jcr/seplogic.pdf),
  introduction and frame rule, distinguishes disjoint accessible
  storage and conditions for unaffected frames. Such ownership
  reasoning motivates specifying a handoff, but a row-value identity
  alone proves neither access isolation nor authentication.

No unknown-source decoder, equality oracle, optimum conditional solver,
archive access or new physical update capability is inferred from these
antecedents or from the recovery equations.

## 追加锚（本行以下为增补区）

## 9. Repeated partners on a complete depth-three one-image fiber

### 9.1 The entire current-row fiber and the reading contract

**Definition 9.1 (fixed row and predecessor target).** Keep the original
finite ordered sources, substitution, occurrence addresses and four-reply
reading of Definition 1.1. Fix the complete cut
$P=\{L,R\}^3$. Let $R_*=(C_*,\pi_*)$ have the perfect depth-three exterior
with one occurrence hole at each $p\in P$. Its complete class partition is

$$
\pi_*=
\bigl\{\{LLL,LRL\},\{LLR\},\{LRR\},
       \{RLL,RRL\},\{RLR\},\{RRR\}\bigr\}.
\tag{NBP.9.1}
$$

Call these six public classes $a,b_1,b_2,c,b_3,b_4$, respectively, as
shorthand for their canonical first-occurrence names. These symbols are
not acquired hidden values. All different classes assert disequality.
For a tuple of actual finite class values $x$, write its filling as

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{NBP.9.2}
$$

The comparison domain and required answer are exactly

$$
\mathcal U_*=
 \{u\in\mathcal T:R_P(\rho u)=R_*\},
\qquad F(u)=R_P(u).
\tag{NBP.9.3}
$$

Thus every actual finite origin compatible with the entire current row
belongs to the domain. There is no additional family promise, source-size
bound, chosen predecessor, or retained origin row. Put
$q_1=LL,q_2=LR,q_3=RL,q_4=RR$; the sibling classes at $q_i$ are
$(a,b_i)$ for $i=1,2$ and $(c,b_i)$ for $i=3,4$.

**Assumption 9.2 (acquired current data, actual export and complete cut).**
Exactly one genuine authenticated $\rho$ update binds the one supplied
origin $u$ to the current register $t=\rho u$. The complete current row
is lawfully acquired on this stationary version. Before the complete
access cut, a producer possesses genuinely acquired same-source,
same-version finite data: either the lossless current tree $t$, or the
current row and one acquired finite subtree value for each of its six
classes. A supplement is computed from those data and actually exported
with the row before their access is lost. Equality in the row is computed
on acquired finite terms, as in Assumption 8.1; there is no hidden-value
equality service.

A separately supplied lawful entry allows a common deterministic reader
to receive $P,R_*$, the exported supplement, and common source-independent
controls. These determine its entire accessible initial state, from
which the declared inputs are recoverable. Authentication certifies the
same origin/register relationship and the single update without revealing
which member of $\mathcal U_*$ is actual. No other source-dependent field
is accessible: origin identity, predecessor data, alpha marker, acquired
values, traces, caches, archives, pointers, control fields, acquisition
order or counts, lengths, meters, timing and update packets add no
undeclared distinction. A field determined by the retained payload adds
no extra distinction; any further accessible field changes this contract.

The same current register is stationary throughout fresh reading. Every
finite address is legal, and its reply is precisely the native
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$ readout at that address.
No further update is allowed. Every invocation counts, including repeats,
absent-address calls and re-reads of addresses used in acquisition. The
reader must terminate and return $F(u)$ for every $u\in\mathcal U_*$.

These are supplied acquisition and access conditions, not consequences of
a row identity. The finite producer of Theorem 8.2 can acquire $t$ using
its native traversal, but its retained full trace does not automatically
implement this narrower export or access cut. Actual export, lawful new
entry, isolation from discarded fields and any entry after absorbing stop
remain separate premises. No resume action is supplied by the stopped
producer itself.

For a supplement $\sigma$, let its conditional alphabet size be
$|\sigma[\mathcal U_*]|$. For integers $r\ge1,q\ge0$, write
$\mathsf{InvFeas}_*(r,q)$ when there exist an acquired/exported supplement
with at most $r$ actual values and one reader whose fresh invocation count
is at most $q$ on every origin in $\mathcal U_*$. Let
$\mathsf Q_*(r)$ be the least such $q$. This is joint encoder/reader
existence, not a performance guarantee for every $r$-value encoder.

### 9.2 Image constraints and all five literal predecessor rows

**Proposition 9.3 (complete image-fiber classification).** Let
$\mathcal I=\rho[\mathcal T]$, with the exact grammar and inverse $\delta$
of Transport--Memory Completion §22, (RA.2207). A filling $t=\mathscr S(x)$
with six pairwise distinct values is in $\mathcal I$ if and only if exactly
one of the following alternatives holds:

1. All six values belong to $\mathcal I$.
2. For exactly one $i\in\{1,2,3,4\}$, $x_{b_i}=\alpha$; its left partner
   is $\beta$; every other class value belongs to $\mathcal I$.

In the second alternative, the left partner is $x_a$ for $i=1,2$ and
$x_c$ for $i=3,4$. Pairwise disequalities still apply, so every other
class is different from that forced beta as well as from the alpha.
In particular, neither $a$ nor $c$ can be the current alpha class.

All five alternatives are attained by actual finite origins. Their
predecessor rows are exactly $R_0,R_1,R_2,R_3,R_4$ defined as follows.
For alternative zero, $R_0=R_*$. For alternative $i>0$, set

$$
O_i=P\setminus\{q_iL,q_iR\}.
\tag{NBP.9.4}
$$

The exterior of $R_i$ is $C_*$ with precisely the pair of holes at $q_i$
replaced by one concrete beta leaf. Its partition is $\pi_*|_{O_i}$,
with canonical names recomputed on $O_i$. All retained equalities and
all retained disequalities are part of this answer. Consequently

$$
|F[\mathcal U_*]|=5.
\tag{NBP.9.5}
$$

**Proof.** The supplied image grammar has disjoint cases beta, the special
block $E=\langle\beta,\alpha\rangle$, and a pair of image subtrees;
alpha is not an image. The root of $t$ and its two depth-one children
are branches whose right children are branches. None is $E$. Applying
the general-pair case successively shows that all four subtrees at $q_i$
are images. At any such subtree the image grammar allows exactly an
$E$ block or a pair of image values. Its left value is therefore always
an image. Its right value is either an image or alpha; alpha occurs
precisely in the $E$ case and forces its left value to be beta.

The complete partition makes the four right-class values distinct, so
at most one is alpha. This proves the necessity of the alternatives,
including the restrictions on both repeated left values. Conversely,
in alternative zero every $q_i$ is a pair of images. In alternative
$i>0$, the $q_i$ block is $E$ and each other $q_j$ is a pair of images.
Pairing upwards puts the entire $t$ in $\mathcal I$. Its unique finite
origin is $u=\delta(t)$, with $\rho u=t$. Literal filling by an injective
class valuation gives exactly $R_*$, including every disequality, by
the native row fiber of Definition 1.2. Thus these sufficient conditions
refer to actual sources, not merely locally consistent formal labels.

Reuse Theorem 3.2's current-alpha/birth criterion and Theorem 2.2's
occurrence repair. In alternative zero all eight cut occurrences are
old. In alternative $i>0$, precisely the two children of the $E$ block
at $q_i$ are newborn. Every other cut occurrence is old, giving (NBP.9.4).
Inverse parsing takes that $E$ to a concrete beta at $q_i$ and preserves
each other exterior bracket, stopping at the old holes. Injectivity of
$\rho$ preserves equality and disequality among their hidden values.
Theorem 2.2 therefore gives exactly the claimed complete rows. Their
reached sets are different, so the five rows are pairwise different.

In particular, when $i=1$ or $2$, only one of the two occurrences of
class $a$ is newborn. The other is an old hole whose current beta value
is the image of an old hidden alpha. One must retain this hole and
recompute its class name, not replace both occurrences of $a$ by a
concrete leaf. The same observation applies to $c$ for $i=3,4$. This is
the occurrence-sensitive repair of §2, not a classwise deletion rule.

For simultaneous finite realizations, use the distinct native orbit
$T_j=\rho^j\alpha$ cited in Theorem 3.3. Here
$T_0=\alpha,T_1=\beta$, and every $T_j$ with $j\ge2$ is a branch in
$\mathcal I$. Set $A=T_2,C=T_3,D_j=T_{j+3}$ for $1\le j\le4$. Define
five tuples, indexed by $h\in\{0,1,2,3,4\}$, by

$$
\begin{aligned}
x_a^{(h)}&=\begin{cases}\beta,&h\in\{1,2\},\\A,&h\notin\{1,2\},\end{cases}\\
x_c^{(h)}&=\begin{cases}\beta,&h\in\{3,4\},\\C,&h\notin\{3,4\},\end{cases}\\
x_{b_j}^{(h)}&=\begin{cases}\alpha,&h=j,\\D_j,&h\ne j.\end{cases}
\end{aligned}
\tag{NBP.9.6}
$$

In each tuple the six values are pairwise distinct: the unmodified values
are distinct orbit elements of index at least two, and the modifications
introduce at most one beta and one alpha. The tuple has exactly alternative
$h$, so $t_h=\mathscr S(x^{(h)})$ is an actual image and
$u_h=\delta(t_h)\in\mathcal U_*$. Its predecessor row is $R_h$. Together
with the exhaustive classification, these witnesses prove (NBP.9.5).
The inverse here constructs proof witnesses; it is not an input given
to the reader or a physical inverse operation. $\square$

### 9.3 Arbitrary native addresses on actual lower-bound witnesses

**Proposition 9.4 (all-address binary bridge).** On the five fixed current
trees $(t_h)_{h=0}^4$ from (NBP.9.6), every finite native address has at
most two different replies. At each of the two occurrences of $a$, a
query can separate the group $\{1,2\}$ from its complement; for $c$ the
corresponding group is $\{3,4\}$. At a $b_j$ occurrence, any nonconstant
query separates only $j$. These are statements about actual native
replies on these witnesses, not about the number of replies on the
whole fiber.

**Proof.** An address $v$ of length less than three is at a common skeleton
branch, and has constant reply $\mathsf{branch}$. Every address of length
at least three has a unique decomposition $v=pw$ with $p\in P$ and
finite suffix $w$. Write $d=[p]_{\pi_*}$. Native descent into the actual
filled hole gives the exact equality

$$
r_{t_h}(pw)=r_{x_d^{(h)}}(w).
\tag{NBP.9.7}
$$

The possible subtree values in this equation are the following two fixed
finite trees, with the stated sets of exceptional indices:

| Class $d$ | Default subtree | Exceptional indices | Exceptional subtree |
| --- | --- | --- | --- |
| $a$ | $A$ | $1,2$ | $\beta$ |
| $c$ | $C$ | $3,4$ | $\beta$ |
| $b_j$ | $D_j$ | $j$ | $\alpha$ |

For any $w$, applying the native four-reply reading to those two trees
gives either one common value or two specified values. No condition
that $w$ be reached is imposed: at a leaf every nonempty suffix gives
absent, and at a branch the finite-tree descent determines the reply,
including any later blocking leaf. All deep, absent and leaf-continuation
cases are therefore included. Repeated class occurrences obey the same
equation, but one address enters just one occurrence cone. Repeated
invocations return the same stationary value and still count as calls.
This covers every finite native address, with no equality, archive or
timing query. In particular the empty-suffix query at $p=LLL$ returns
beta on $h=1,2$ and branch on $h=0,3,4$, giving an actual two-versus-three
split. $\square$

For clarity, the full domain is not a binary-reply native system. At
address $LLRR$, inside the right child of class $b_1$, choose respectively
$x_{b_1}=\beta,E,\langle\beta,\beta\rangle,
\langle\beta,E\rangle$. These are four different image values and give
absent, alpha, beta and branch, respectively. Choose the five remaining
class values to be mutually distinct higher orbit elements, different
from those four trees. All six values are then images and Proposition 9.3
puts all four fillings in the full actual fiber. The binary bridge is a
lower-bound restriction to five realizations, not a restriction of the
reader's native interface or of $\mathcal U_*$.

### 9.4 Exact joint supplement and fresh-invocation frontier

**Theorem 9.5 (attained full-fiber frontier).** Under Assumption 9.2, for
all integers $r\ge1,q\ge0$,

$$
\mathsf{InvFeas}_*(r,q)\quad\Longleftrightarrow\quad r\,2^q\ge5.
\tag{NBP.9.8}
$$

Equivalently, the exact least worst-case fresh invocation count is

$$
\mathsf Q_*(r)=
\begin{cases}
3,&r=1,\\
2,&r=2,\\
1,&r=3\text{ or }4,\\
0,&r\ge5.
\end{cases}
\tag{NBP.9.9}
$$

**Proof, necessity.** Restrict any feasible acquired encoder and reader to
the actual finite origins $u_0,\ldots,u_4$ of Proposition 9.3. For each
used supplement value $s$, put
$H_s=\{h:\sigma(u_h)=s\}$. The nonempty $H_s$ partition five indices
into at most $r$ parts, even if $\sigma$ depends on every acquired current
class value. All initial reader inputs are identical within one part.
Its required rows $R_h$ are different, so it must distinguish all indices
in that part using its native replies.

At any chosen address, Proposition 9.4 supplies at most two possible
replies on the witnesses. Encode its default reply by zero and its
possible different reply by one, using zero alone in the constant case.
Given the address, this bit reconstructs the entire native reply. At an
adaptive history, the next address is determined by the common initial
state and reconstructed previous replies, so the correspondence holds
at every subsequent query, not only along a designated path. Histories
with no realizing witness can be assigned constant zero questions.
After the reader stops, pad the mathematical transcript to length $q$
with constant zeros; these padding symbols are not native invocations.

The resulting length-$q$ transcripts are injective on $H_s$. If two
were identical, deterministic reconstruction would give the same native
history and stopping decision for both. Early stopping adds no extra
symbol: once that common history determines a stop, both candidates
stop there with the same output. This contradicts the different rows.
The argument accommodates absence and repeated invocations through the
all-address bridge and counts every real invocation before padding.

Apply the existing
[BinaryProtocolDepthLowerBound](../../../D5/S3/ConceptDynamics/Coding/BinaryProtocolDepthLowerBound.lean),
`adaptive_binary_protocol_depth_lower_bound`, to the finite source type
$H_s$, constant already-known concept, target $h\mapsto R_h$ and the
adaptive binary transcript just constructed. Its worst fiber diversity
is $|H_s|$, so it gives $\lceil\log_2|H_s|\rceil\le q$, equivalently
$|H_s|\le2^q$. Summing over the nonempty parts yields

$$
5=\sum_s|H_s|\le |\{s:H_s\ne\varnothing\}|\,2^q\le r\,2^q.
\tag{NBP.9.10}
$$

This uses the existing binary identification capacity, not a new generic
counting theorem. The five witnesses are alternative fixed sources with
their own truthful acquisition and export. No source changes during a
reading run, and no equality of discarded acquisition records is assumed.

**Proof, full-domain attainments.** By Proposition 9.3, the acquired current
data determine the unique label $h\in\{0,1,2,3,4\}$: inspect the acquired
right-class values for alpha, taking $h=0$ if none is alpha. This is a
finite computation on genuinely acquired terms, not a free retained
marker. The encoders below export only their specified block index.
Their tables and the five complete row outputs are public finite data
computed from $P,R_*$ using Proposition 9.3 and Theorem 2.2. Every label
is actually attained, so each listed block is nonempty on $\mathcal U_*$.

For $r=1$, export one common value. First query $LLL$, a representative
root of class $a$. Its value is an image, so the reply is beta or branch.
If it is beta, the actual label lies in $\{0,1,2\}$: a selected $3$ or
$4$ would force $x_c=\beta=x_a$, contradicting the retained disequality.
If it is branch, the actual label lies in $\{0,3,4\}$: a selected $1$
or $2$ would force $x_a=\beta$.

In the beta case, query the root at $q_1R=LLR$; an alpha reply identifies
$h=1$ and stops. Otherwise query $q_2R=LRR$; alpha identifies $h=2$ and
any other reply gives $h=0$. In the branch case perform the same tests
at $q_3R=RLR$ and $q_4R=RRR$, returning $3,4$ or $0$. All these roots
are reached. Non-alpha replies may be beta or branch; their distinction
is not needed. Each source is classified correctly with at most three
calls. In particular $h=0$ remains possible on both outcomes of the
first query: an image filling with no alpha may still have $x_a=\beta$.
The strategy does not pretend to make a target-only group test on the
entire fiber. On $u_0$ it makes all three calls, attaining this bound.

For $r=2$, export the block of the actual label in
$\{0,1,2\}\mid\{3,4\}$. In the first block, test $b_1$ and then, if
needed, $b_2$ at their cut roots for alpha; if neither is alpha, return
zero. In the second block test $b_3$ for alpha; otherwise infer $4$.
This is correct on every origin of the full fiber with at most two
calls, and $u_0$ attains two.

For $r=3$, use $\{0\}\mid\{1,2\}\mid\{3,4\}$. The singleton block
needs no query; in either two-member block test its first right-class
root for alpha and infer the other member on a non-alpha reply. The
worst count is one, attained on both non-singleton blocks. For $r=4$
one may use the four nonempty blocks
$\{0\}\mid\{1\}\mid\{2\}\mid\{3,4\}$, again with worst count one.
For $r\ge5$, export the actual label itself, using five values, and
return its complete row with zero fresh invocations. This last endpoint
is the attained predecessor/current-alpha correspondence of Theorem 3.2
and the zero-query acquired-record recovery of Theorem 8.2.

Each construction uses one common deterministic reader and actual
pre-cut export from the supplied current data. After identifying $h$ it
returns the entire $R_h$, including canonical restricted class names,
all disequalities and the absent-cut guards from its concrete beta leaf.
The reader never asks for a predecessor tree or an unknown-subtree
comparison. Necessity rules out two calls when $r=1$, one when $r=2$,
and zero when $r=3,4$. For $r\ge5$ zero is minimal. This proves (NBP.9.9).
For integer $q\ge0$ these cases are exactly $r2^q\ge5$; a strategy with
fewer than $q$ calls already satisfies the upper budget, with no extra
calls required. Hence (NBP.9.8) follows. $\square$

### 9.5 Transfer failure, attribution and resource boundaries

**Corollary 9.6 (target cardinality does not transfer the forward law).**
The cardinality $m=|F[\mathcal U_*]|=5$ does not by itself force
$r(q+1)\ge m$ for predecessor-row recovery on a complete actual
one-image current-row fiber. Here $r=1,q=3$ is feasible while
$r(q+1)=4<5$.

**Proof.** Proposition 9.3 proves the exact full-domain target count and
Theorem 9.5 supplies the constant-supplement three-call reader on that
same domain. On its actual witnesses, reading $LLL$ separates two
origins from three, as Proposition 9.4 shows; it is not a
singleton-or-constant question. On the full fiber the same query gives
the legal three-label covers $\{0,1,2\}$ and $\{0,3,4\}$, followed by
native right-root tests. The image constraint and retained left-class
disequality are the reason these covers are valid.

[Native Alpha Recut Memory, Theorem 9.4](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
retains its original hypotheses and conclusion. It starts with the
unrestricted old-row fiber and asks for the next entire row after one
update. Its Proposition 9.3 constructs updated witnesses on which every
native address is singleton-or-constant. The present task starts with a
fixed current row, restricts the current source to an actual image, and
asks for its predecessor row. The repeated partners impose relations
between the feasible alpha label and the other hidden values, so the
forward witness bridge is not available for this inverse target.
This counterexample concerns transfer of a cardinality-only law, not
the validity of the forward theorem. $\square$

**Mathematical citation 9.7 (suppliers and precise scope).** The native
finite source, legal row fibers, equality/disequality convention and
occurrence-sensitive inverse are the suppliers in Definitions 1.1--1.2,
Theorems 2.2 and 3.2, and Transport--Memory Completion §22. The forward
alpha-collision recurrence and its acquired extraction and two endpoint
optima are supplied by Native Alpha Recut Memory §§2--7; its §9 supplies
the separate forward joint frontier. None of those results is rederived
as a generic theorem here. The ordinary source-specific deduction is the
exhaustive repeated-partner image classification, the five actual finite
realizations and their all-address binary bridge, and the matched
encoder/reader strategies on the entire actual fiber.

The classical finite-label and adaptive decision-tree methods are
intermediate suppliers. The invocation/retention distinction and
fixed-encoder caution are already explicit in
[Word Retention and Geometric Reaccess §4](RECURSIVE_RELATIONAL_OBSERVATION_WORD_RETENTION_AND_GEOMETRIC_REACCESS.md).
The binary depth lower bound used above is the cited existing
`adaptive_binary_protocol_depth_lower_bound`, with its finite-domain
hypotheses supplied by the actual five witnesses. General query geometry
is a mature precedent: Robert Nowak, *The Geometry of Generalized Binary
Search*, [arXiv:0910.4397v5](https://arxiv.org/abs/0910.4397v5), §V.A,
printed p.14 / PDF p.15, contrasts disjoint-interval singleton testing
and its linear query cost with richer dyadic tests and logarithmic
identification. That passage motivates checking the actual permitted
queries; it supplies neither a new native subset-query port nor the
image constraints or numerical frontier of this example. Here the
split is realized by an ordinary address in the unchanged four-reply
native interface. These are source-specific ordinary deductions using
known methods, with no claim of literature priority.

The alphabet bound counts only exported supplemental values conditional
on the already acquired row. It does not bound total controller states,
programs, workspace, addresses, row/register storage, authentication,
outputs or physical memory. With no fresh reading the five labels need
three fixed-width supplemental bits; this is an alphabet representation
count only. Producer acquisition, local term comparison, export, retained
payload access, permissions and address transmission remain separate
costs. Zero fresh calls do not imply zero acquisition or total work;
three abstract calls do not imply a corresponding bound on physical
time. No native-to-physical resource equivalence is supplied.

Theorem 9.5 optimizes encoder and reader jointly. An encoder that is
constant still has the three-call lower bound even if an alphabet of
capacity five is available. Neither unused alphabet values nor balanced
block cardinalities alone prove a fixed arbitrary encoder's performance.
The witnesses used for necessity do not weaken the full-fiber contract;
the strategies used for sufficiency cover every actual origin in it.
Changed cuts, extra accessible data, later images, further updates,
randomization and address-weighted prices require their own analysis.

[Native Alpha Recut Memory §10](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
has the distinct elapsed-update target from two acquired rows across
possibly different cuts, with no supplied numeric update count. Its
two endpoint rows are additional inputs for that separate target.
They are not predecessor-query coverage and are not added to the inputs
of Assumption 9.2. This appendix uses only the fixed complete current row,
the expressly acquired/exported supplement and fresh stationary native
replies after exactly one authenticated update.

## 追加锚（本行以下为增补区）

## 10. Exact class-root experiments on every full actual one-image fiber

### 10.1 The full fiber, root types and actual image admissibility

**Definition 10.1 (fixed complete row and full one-image domain).** Keep the
finite ordered trees, $\rho$, literal occurrence addresses and four-reply
native port of Definition 1.1. Fix any finite prefix-free public cut $P$
and any complete current row $R_*=(C_*,\pi_*)$. Its reached support is
$H\subseteq P$; its exterior includes every concrete bracket and leaf
outside those holes, and a strict-prefix blocking leaf for every
$p\in P\setminus H$. Let $D$ be the finite set of classes of $\pi_*$,
$k=|D|$, and write $[p]\in D$ for the class of $p\in H$. Fix the first
occurrence $p_d$ of each class as its representative. Empty cuts, a root
cut, zero classes and blocked cut members are allowed.

For an injective class valuation $x:D\to\mathcal T$, set

$$
\mathscr F_*(x)=C_*[(x_{[p]})_{p\in H}],\qquad
\mathcal X_*=\{x:D\to\mathcal T:
 (\forall d\ne e,\ x_d\ne x_e)\ \land\ \mathscr F_*(x)\in\mathcal I\},
\quad \mathcal I=\rho[\mathcal T].
\tag{NBP.10.1}
$$

The nonempty comparison domain and whole target are exactly

$$
\mathcal U_*=\{u\in\mathcal T:R_P(\rho u)=R_*\},\qquad F(u)=R_P(u).
\tag{NBP.10.2}
$$

The actual legal-row fiber of Definition 1.2 and the image inverse
$\delta$ of Transport--Memory Completion (RA.2207) give the bijection

$$
x\longmapsto u_x=\delta(\mathscr F_*(x)),\qquad
u\longmapsto x_d=(\rho u)|_{p_d},
\qquad \mathcal X_*\cong\mathcal U_*.
\tag{NBP.10.3}
$$

This retains every repeated occurrence, every different-class disequality
and every absent-cut guard. All finite origins in (NBP.10.2) remain in the
domain; there is no bound on source size, rank or hidden history.

For a finite tree $z$, write
$\operatorname{rt}(z)\in\{\alpha,\beta,\mathsf{br}\}$ for its root
constructor. A class-root type is a map
$\theta:D\to\{\alpha,\beta,\mathsf{br}\}$. In the finite exterior term
$C_*$, replace every hole occurrence by its shared class name. For a
subterm $e$, let $\operatorname{lit}_\ell^\theta(e)$, with
$\ell\in\{\alpha,\beta\}$, mean that $e$ is the concrete leaf $\ell$,
or $e$ is a class name $d$ with $\theta(d)=\ell$. A pair is never a
literal leaf. Define the finite image predicate by

$$
\begin{aligned}
\operatorname{im}^\theta(\alpha)&=\mathsf{false},&
\operatorname{im}^\theta(\beta)&=\mathsf{true},&
\operatorname{im}^\theta(d)&\Longleftrightarrow\theta(d)\ne\alpha,\\
\operatorname{im}^\theta(\langle e,f\rangle)
&\Longleftrightarrow
 \bigl(\operatorname{lit}_\beta^\theta(e)\land
       \operatorname{lit}_\alpha^\theta(f)\bigr)
 \ \lor\
 \bigl(\operatorname{im}^\theta(e)\land
       \operatorname{im}^\theta(f)\bigr).
\end{aligned}
\tag{NBP.10.4}
$$

Its disjuncts are the special block $E=\langle\beta,\alpha\rangle$
and the general pair of image trees. Define the finite admissible chart

$$
\Theta_*=\{\theta:
 \operatorname{im}^\theta(C_*)\ \land\
 |\theta^{-1}(\alpha)|\le1\ \land\
 |\theta^{-1}(\beta)|\le1\}.
\tag{NBP.10.5}
$$

The two leaf restrictions concern distinct classes, not occurrences.
They do not impose different values on different residual names that
could occur in an auxiliary construction.

**Proposition 10.2 (exact type feasibility and exact filling test).**
For every injective actual finite valuation $x$, with
$\theta_x(d)=\operatorname{rt}(x_d)$,

$$
\mathscr F_*(x)\in\mathcal I
\quad\Longleftrightarrow\quad
\left(\forall d\text{ with }\theta_x(d)=\mathsf{br},\
 x_d\in\mathcal I\right)
\land\operatorname{im}^{\theta_x}(C_*).
\tag{NBP.10.6}
$$

Moreover,

$$
\Theta_*=\{\theta_x:x\in\mathcal X_*\}.
\tag{NBP.10.7}
$$

Thus the chart decides whether a prescribed complete class-root assignment
has an actual-image realization, for any fixed exterior and complete
partition. Root type alone does not certify image membership of an
arbitrary branch-valued filling.

**Proof.** Reuse the exact grammar
$\mathcal I::=\beta\mid E\mid\langle\mathcal I,\mathcal I\rangle$
and its disjoint parser from (RA.2207). Induction on that grammar shows
that every subtree of an image is either $\alpha$ or an image:
the children of $E$ are $\beta,\alpha$, and the children of a general
image pair are images to which the induction applies. Consequently every
branch-valued class subtree of an actual image is itself an image.
A leaf-valued class is exactly its declared literal leaf. Induction on
the finite exterior then identifies image membership at each visible
subterm with (NBP.10.4): a pair is $E$ precisely in the first disjunct,
and otherwise it is an image precisely when both children are images.
This proves necessity in (NBP.10.6). The same exterior induction gives
sufficiency when every branch-valued class is an image. Injectivity makes
at most one distinct class equal to either leaf, proving the inclusion
from right to left in (NBP.10.7).

For the other inclusion, fix $\theta\in\Theta_*$. Give its leaf-valued
classes their forced literal leaves. Give its branch-valued classes
pairwise distinct finite non-atomic image values, obtained simultaneously
from Retained Literal Root Depth Theorem 2.2 with prescribed intrinsic
rank one; its construction writes these values as $\rho p_i$ with
arbitrarily deep leaves. They are branches, mutually distinct, and
distinct from both leaves. Equation (NBP.10.6) makes the resulting
injective filling an actual image. The native legal-row fiber and
$\delta$ then produce an actual finite origin with exactly $R_*$.
This proves (NBP.10.7), including zero branch classes and zero classes.
For the last distinction in the statement, take a root hole. Its type
$\mathsf{br}$ is feasible, but $\langle\alpha,\alpha\rangle$ is a
branch outside the image: it is neither $E$ nor a pair of images.
Equation (NBP.10.6) requires the actual branch filling to be an image
as well as its root assignment to be feasible. $\square$

### 10.2 The whole predecessor target and simultaneous deep actual witnesses

**Definition 10.3 (type target and occurrence mask).** For
$\theta\in\Theta_*$ let $A_\theta$ be its unique alpha class, or
$\bot$ when it has none. At a visible root $q$ of $C_*$, use
$\operatorname{Alpha}_{C_*}(q,A_\theta)$ exactly as in Definition 3.1.
For a reached nonroot cut occurrence $p=qd$, its parent and sibling
root are visible: prefix freedom forbids a cut ancestor. Put

$$
O_\theta=
 H\setminus\{qd\in H:d\in\{L,R\},\
             \operatorname{Alpha}_{C_*}(qR,A_\theta)\},
\qquad
G_*(\theta)=\operatorname{Back}_P(R_*,O_\theta).
\tag{NBP.10.8}
$$

The root, when cut, belongs to $O_\theta$. The public partial decoder
$\operatorname{Back}_P$ is evaluated only on these attained masks.

**Theorem 10.4 (complete predecessor factorization).** For every
$x\in\mathcal X_*$ and its actual origin $u_x$,

$$
H_P(u_x)=O_{\theta_x},\qquad F(u_x)=G_*(\theta_x).
\tag{NBP.10.9}
$$

In particular the finite target set is
$G_*[\Theta_*]=F[\mathcal U_*]$, and its size equals the number of
attained labels $A_\theta$, as in Theorem 3.2.

**Proof.** Apply Theorem 3.2 directly to the actual image
$t=\mathscr F_*(x)=\rho u_x$. Its current alpha label is $A_{\theta_x}$,
so (NBP.3.1) gives exactly the first equality in (NBP.10.9).
At a visible parent of a reached cut, an alpha right child forces the
whole parent to be $E$ by the image grammar; its two children were born
from a predecessor beta leaf. Other reached cut occurrences are old.
Every currently blocked member of $P\setminus H$ was also absent in
the predecessor because old positions persist.

Theorem 2.2 applied to this same transition gives
$\operatorname{Back}_P(R_*,O_{\theta_x})=R_P(u_x)$. Its occurrence
repair preserves old holes even when an old and a newborn occurrence
share one current class; it canonically renames the restricted classes
and retains all their equalities and disequalities. Its inverse exterior
has the concrete beta parent of every newborn child, hence the complete
guards for predecessor-blocked cuts, together with the guards for cuts
already blocked in $C_*$. This is the whole row in the second equality,
not just its newborn mask or alpha label. Proposition 10.2 makes every
$\theta$ attained, and Theorem 3.2 supplies the stated target-label
bijection. $\square$

**Proposition 10.5 (simultaneous image-valued deep padding and query
correspondence).** For every $L\ge0$ there are actual valuations
$x^\theta\in\mathcal X_*$, one for every $\theta\in\Theta_*$, such that
$\theta_{x^\theta}=\theta$ and all their branch-valued classes have
minimum native leaf depth greater than $L$. Each valuation retains all
class disequalities and repetitions. Write
$t^\theta=\mathscr F_*(x^\theta)=\rho u^\theta$.

For every native address $v$ with $|v|\le L$, its reply on these actual
trees is either constant in $\theta$, or a known function of one
class-root type. More precisely, if exterior traversal first enters a
hole $p\in H$, write $v=pw$ and $d=[p]$. Then

$$
r_{t^\theta}(v)=
\begin{cases}
\theta(d),&w=\varepsilon,\\
\mathsf{absent},&w\ne\varepsilon,\ \theta(d)\in\{\alpha,\beta\},\\
\mathsf{branch},&w\ne\varepsilon,\ \theta(d)=\mathsf{br}.
\end{cases}
\tag{NBP.10.10}
$$

The symbols $\mathsf{br}$ and $\mathsf{branch}$ denote the same
constructor reply. If traversal does not enter a hole, the complete
finite exterior supplies the reply, including every blocking absence.

**Proof.** Apply Retained Literal Root Depth Theorem 2.2 simultaneously
to the finitely many branch slots $(\theta,d)$. Prescribe intrinsic
rank one in every slot, minimum leaf depth greater than $L$, and include
all within-valuation different-branch-class negatives. Its explicit
construction gives finite non-atomic image values, indeed it can make
all slots pairwise distinct. Use one value at every repeated occurrence
of the same class in each valuation, and the forced literals in the
leaf slots. Proposition 10.2 puts every resulting filling in the
original full image fiber. No cross-origin relation is required.
Theorem 10.4 gives precisely $G_*(\theta)$ on each of these origins.

Exterior traversal is independent of the filling until it first reaches
a hole. If it enters one, native subtree descent is exactly
$r_{t^\theta}(pw)=r_{x^\theta_d}(w)$. At an empty suffix this is the
root type. A nonempty suffix at a literal leaf is absent. At a padded
branch value, $|w|\le|v|\le L$ and the minimum leaf depth is greater
than $L$, so its endpoint is a reached branch. If no hole is entered,
the visible endpoint or earlier concrete blocking leaf in $C_*$
determines the reply. These cases exhaust all finite addresses of the
stated length, including root, absent addresses, extensions of leaves,
and repeated-class cones. $\square$

The representatives establish actual feasibility and a bounded-menu
query correspondence. They do not reconstruct all sources as themselves.
The root chart and the selected $u^\theta$ are therefore distinct from
the exact source charts of Symbolic Feedback Synthesis Definition 3.1
and Proposition 3.2, whose two directions reconstruct each actual
source. No completed, infinite or rational tree is a source witness here.

### 10.3 The acquired/exported contract and the finite experiment task

**Assumption 10.6 (paid acquisition, actual export and complete entry).**
Exactly one authenticated genuine $\rho$ update binds the origin
$u\in\mathcal U_*$ to the stationary current register $t=\rho u$.
The complete row is lawfully acquired. Before a complete access cut,
the producer possesses actually acquired same-source, same-version
finite data: either the lossless current tree or $R_*$ and one acquired
finite subtree value for every class in $D$. It may perform finite
local computation and compare these acquired terms, computes the
supplement, and actually exports its complete value with $R_*$ before
losing access to the acquired values. Equality in the complete partition
comes from acquired values, not an unknown-subtree equality service.

A supplied common lawful reader entry exposes exactly $P,R_*$, the
exported supplement and common source-independent controls, from which
these inputs are recoverable. Its entire accessible initial state is
determined by these inputs. No other source-dependent identity, old row,
alpha label, value, trace, cache, archive, pointer, control, acquisition
order or count, length, meter, timing or update packet is available.
A field determined by the retained payload adds no new distinction;
any further accessible field changes this contract. Authentication
certifies continuity and the one update without selecting an origin
inside the fiber.

The same current register stays stationary during fresh reading.
Every finite address is legal and returns its native four-reply value.
Every invocation counts, including repeats, absences and addresses
already used in acquisition. No further update, equality, image,
provenance, pointer, physical inverse or other source port is supplied.
The reader must terminate with the whole $F(u)$ for every origin in
the full fiber. Common installation, lawful new entry after any
absorbing producer stop, acquisition, local computation, export and
access isolation are supplied and paid premises, not consequences
of the row identity. This is Assumption 9.2 for the general row.

For $r\ge1,q\ge0$, define $\mathsf{InvFeas}_*(r,q)$ by joint existence
of a deterministic acquired/exported supplement with at most $r$
distinct actual complete values on $\mathcal X_*$ and a deterministic
reader with at most $q$ fresh invocations on every $u\in\mathcal U_*$.
The supplement may depend on all acquired values, not just root types.

**Definition 10.7 (finite class-root experiment feasibility).** The
finite task has input $\theta\in\Theta_*$, whole-row target
$G_*(\theta)$, and experiment menu $D$. Experiment $d$ returns
$\theta(d)$ and costs one invocation; repetitions also cost one.
Let $\mathsf{RootFeas}_*(r,q)$ mean that there exist a finite label
set $S$ with $1\le|S|\le r$, a coloring $c:\Theta_*\to S$, and, for
each used $s$, a finite deterministic experiment tree $E_s$ of depth
at most $q$, such that $E_{c(\theta)}$ returns $G_*(\theta)$ for every
$\theta\in\Theta_*$. Internal vertices ask one class $d\in D$,
edges carry the three reached root replies, and leaves carry complete
row outputs. Early halts are allowed. Impossible edges may halt
arbitrarily. For zero classes only the no-query tree exists.

This is a finite task, with at most $3^k$ inputs and $k$ experiments.
It supplies neither an arbitrary subset query nor a class equality
test. It is a task on root types, not an exact source chart.

### 10.4 Both directions of the same-$r,q$ correspondence

**Theorem 10.8 (exact full-fiber joint feasibility reduction).** Under
Assumption 10.6, for every integer $r\ge1,q\ge0$,

$$
\mathsf{InvFeas}_*(r,q)\quad\Longleftrightarrow\quad
\mathsf{RootFeas}_*(r,q).
\tag{NBP.10.11}
$$

Both sides have the same supplement capacity and the same fresh
invocation upper budget. The left side includes every finite actual
origin, every legal finite address and every full-value-dependent
acquired/exported supplement permitted by the contract.

**Proof, from the finite task to the full actual fiber.** Fix a coloring
and trees witnessing $\mathsf{RootFeas}_*(r,q)$. The producer computes
$\theta_x$ by inspecting the roots of the already acquired class
values. No fresh source call is used for this local inspection and
no unknown value is compared. It exports the complete finite code
$c(\theta_x)$, using distinct installed finite values for the used
labels. There are at most $r$ values. Every used type is actually
attained by Proposition 10.2, so the actual code range is exactly
the used coloring range.

On entry with that code, the common reader follows its installed
tree. At experiment $d$ it actually invokes the native port at
$p_d$. This address is reached on every current source in the fiber,
and its reply is exactly $\theta_x(d)$. Each traversal of a query
vertex is one counted invocation, even if that class was queried
before. Induction on the reply path makes execution agree with
$E_{c(\theta_x)}$. It stops after at most $q$ calls with
$G_*(\theta_x)=F(u_x)$ by Theorem 10.4. The output includes all
exterior syntax, canonical restricted classes, disequalities and
absence guards. The acquisition/export and common-entry premises
implement the finite code without adding any source-bearing field.

**Proof, from an arbitrary full-fiber protocol to the finite task.**
Fix a feasible supplement $\sigma$ and reader; enumerate their $a$
actually used complete supplement values as $s_1,\ldots,s_a$, where
$1\le a\le r$. For each value, unroll only reachable native reply
histories of the reader. At a reachable history its common initial
state, complete supplement and previous replies determine its next
local segment, finite query word or halt, and any halt output.
Some actual origin realizes that history. Source-total termination
on that origin makes the determined local segment finite. The
uniform bound $q$ leaves only finitely many reachable histories:
for each advice value there are at most
$1+4+\cdots+4^q$ reply words. Replace unreachable children by
immediate arbitrary halts. Thus there are finitely many fixed
query words over all these finite trees. This is the bounded
unrolling used in Native Signed Feasibility Theorem 7.3, with no
new update and with advice values as finitely many separate entries.

Let $L$ be the maximum length of these query words, taking $L=0$
if there are none. No source-size bound has been introduced:
$L$ bounds the finitely many words of this fixed comparator.
Use Proposition 10.5 at this common $L$, obtaining one actual
padded origin $u^\theta$ for every $\theta\in\Theta_*$. Define
$c(\theta)=i$ precisely when the actual export on this origin is
$\sigma(x^\theta)=s_i$. This coloring is a finite table with at
most $r$ labels, even though the original $\sigma$ can depend on
all acquired values and can vary among sources of one root type.

Transform the finite reader tree for $s_i$ into a root-experiment
tree as follows. A query at $v$ not entering an exterior hole has
the constant reply determined by $C_*$, so select that child
without an experiment. A query entering any occurrence of class $d$ with empty suffix
asks $d$ and forwards its type reply. A query entering an occurrence
of class $d$ with nonempty suffix asks $d$, forwards
$\mathsf{absent}$ on either leaf type and $\mathsf{branch}$ on
branch type. The third case uses (NBP.10.10). Every transformed
vertex therefore uses zero or one root experiment for one original
native invocation. All original words are within $L$. The
transformation is on the finite tree, so its depth is at most $q$;
retaining repeated questions is legal, and skipping known constants
only decreases the count.

For $\theta$ with $c(\theta)=i$, induction along the transformed
tree reproduces exactly the original reader path on the one fixed
actual origin $u^\theta$ with its truthful acquired/exported value
$s_i$. Every such path was reachable and hence was included in
the unrolling. The original reader returns
$F(u^\theta)=G_*(\theta)$, so the transformed root tree returns
that complete row. Doing this for every $\theta$ proves
$\mathsf{RootFeas}_*(r,q)$.

The padded origins are alternative actual sources, each fixed
through its own run. They are used only for necessity; sufficiency
above covers all actual origins. Selecting them does not assert
that an arbitrary prescribed supplement is constant on type cells.
The new acquired encoder in the first direction can export the
finite coloring found in the second, rather than preserve the
original encoder pointwise. This is exactly why joint existence,
rather than fixed-advice performance, is the invariant. $\square$

The argument is an existence proof of a finite certificate from
a promised correct bounded comparator. It is not an algorithm
that extracts all reachable histories or a useful word bound from
arbitrary program text. No trace, full native behavior, total
controller state count or physical resource correspondence is
preserved by the two directions.

### 10.5 Effective finite criterion, endpoints and the numerical application

**Corollary 10.9 (effective joint root-protocol criterion).** From the
finite input $P,R_*$ with its nonempty actual image fiber and
integers $r\ge1,q\ge0$, the joint feasibility question is decidable
and a positive answer supplies a finite acquired encoder and
stationary native reader under Assumption 10.6. This requires no
supplied source bound or physical word-length bound.

To express the criterion using the existing finite decision-tree
supplier, form the finite relation table

$$
\mathcal J_*=\{(G_*(\theta),(\theta(d))_{d\in D}):
                         \theta\in\Theta_*\}.
\tag{NBP.10.12}
$$

For a coloring $c:\Theta_*\to\{1,\ldots,r\}$, let
$\mathcal J_{c,i}$ consist of its rows with $c(\theta)=i$. Use
the existing finite minimax call value $V$ in (SLH.69.17), with
experiment menu $D$ and four-reply alphabet whose absent classes
are empty. Then the exact criterion is

$$
\mathsf{InvFeas}_*(r,q)
\quad\Longleftrightarrow\quad
\exists c:\Theta_*\to\{1,\ldots,r\}\quad
 \max_{i:\mathcal J_{c,i}\ne\varnothing}
       V(\mathcal J_{c,i},D)\le q.
\tag{NBP.10.13}
$$

**Proof.** Enumerate the at most $3^k$ type assignments and test
(NBP.10.5); Proposition 10.2 makes this an exact finite table of
attained types. Compute $G_*$ using (NBP.10.8), Theorems 2.2 and
3.2. Enumerate the finitely many colorings. On each nonempty
colored subtable, the finite unit-call recurrence (SLH.69.17)
terminates and gives its exact optimal experiment tree: equal
complete menu replies give equal type and hence equal target.
Its constant-target case gives zero calls. Its nonconstant-target
case chooses an actual class-root experiment splitting the table.
Thus it supplies exactly the trees of Definition 10.7, not a
new unrestricted partition action. Theorem 10.8 proves
(NBP.10.13), and its first direction installs the finite encoder
and trees on the full actual fiber. The encoder inspects only
actually acquired terms; the online reader calls only $p_d$.
There are no source-feasibility or equality queries at run time.
$\square$

This directly reuses the bounded literal-task, class-coordinate
and finite protocol methods of Sparse Literal History Transport
§§69.1--69.4 and its existing minimax recurrence (SLH.69.17);
Theorem 74.4 supplies the separate whole-row determining-prefix
framework. The finite unrolling and actual terminal-output
discipline are the suppliers in Native Signed Feasibility
§§7.1--7.3. Its supplied-word-length finite-box enumeration by
itself would not justify (NBP.10.13): it would only test successive
word bounds. Here Proposition 10.5 and Theorem 10.8 replace
arbitrary-address joint feasibility by the finite installed menu
of class roots. This is a source-specific delta with the actual
consumer (NBP.10.13), not a new generic unbounded-word decision
method: SLH §69 already owns unrestricted-depth bounded
literal-task finite decision. The delta is the one-image
admissibility correspondence, simultaneous actual image padding,
and joint acquired/exported advice transfer for the whole
predecessor target.

**Corollary 10.10 (edge cuts, exact zero-query endpoint and constant
supplement).** Set $m=|G_*[\Theta_*]|=|F[\mathcal U_*]|$, so
$1\le m\le k+1$. The result includes the following cases.

1. If $P=\varnothing$, the row exposes the entire finite current
   tree. There is one empty valuation and one actual origin
   $\delta(C_*)$. Its predecessor row is computable from the
   acquired current tree with $r=1,q=0$.
2. If $P=\{\varepsilon\}$, the reached root is always old.
   The feasible current root types are beta and branch, but
   both give the same one-hole predecessor row. Thus
   $r=1,q=0$ is feasible.
3. If $D=\varnothing$ even for a nonempty blocked cut, the
   exterior is the entire current tree and the type chart has
   one empty element. The entire predecessor row and all
   blocked guards are fixed, so $r=1,q=0$ is feasible.
4. For arbitrary blocked cut members, $P\setminus H$ remains
   absent in the predecessor. Members of $H\setminus O_\theta$
   become predecessor-absent with a beta blocking parent.
   These guards are part of every installed $G_*(\theta)$.
5. For $q=0$, feasibility is exactly $r\ge m$. For $r=1$,
   feasibility is exactly $V(\mathcal J_*,D)\le q$, and some
   protocol always uses at most $k$ calls by asking each class
   root once. No acquisition or total-state bound follows
   from either endpoint.

**Proof.** The first three cases follow from the unique image
inverse and the root-old criterion, with the empty product
interpreted literally. The fourth was proved in Theorem 10.4.
For the fifth, a zero-call leaf must have a constant whole target
on its export block, and all $m$ attained targets need different
values. This is the existing finite-answer capacity argument
used in §6, applied to these actual targets. Conversely, the
acquired root chart determines the target, so its target index
can be computed and actually exported using exactly $m$
complete values. With one value there is the entire finite
table and its minimax tree. Asking its $k$ reached class roots
determines the full type and hence the target; every such
invocation is counted. $\square$

**Corollary 10.11 (the established depth-three frontier as an
application).** For the row of Definition 9.1, the finite
criterion gives exactly the previously established frontier

$$
\mathsf{InvFeas}_*(r,q)\Longleftrightarrow r2^q\ge5.
\tag{NBP.10.14}
$$

**Proof.** Proposition 9.3 identifies the attained target rows
as $R_0,\ldots,R_4$. Its five witnesses are actual entries
of the chart, with arbitrary branch fillings still in the
full fiber. Proposition 9.4 restricts every address on those
witnesses to at most two replies, so the binary protocol-depth
supplier used in Theorem 9.5 gives the necessity
$r2^q\ge5$ even for full-value-dependent export. The root
experiments and acquired block encoders in the full-domain
attainments of Theorem 9.5 give sufficiency. They are allowed
trees and colorings in Definition 10.7. Theorem 10.8 carries
them to and from the complete actual fiber at the same
$r,q$, giving (NBP.10.14) as an application of the already
established result. $\square$

This example does not turn the general finite criterion
into a target-cardinality-only law. Its repeated partner
classes supply particular experiments; a different
$\Theta_*$ and menu can have different query geometry.

### 10.6 Suppliers, attribution and the remaining controller boundary

**Mathematical citation 10.12 (ordinary source-specific content
and bounded attribution).** The native algebra and complete
row-fiber bijection are the suppliers in §§1--3.
[Transport--Memory Completion §22](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)
owns image grammar, unique inverse and the old/new node criterion.
[Retained Literal Root Depth Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md)
owns simultaneous prescribed-rank deep finite witnesses
with all negatives; the use here prescribes rank one and
keeps the shared class names and full disequalities.
[Symbolic Feedback Synthesis §§3.1--3.2](RECURSIVE_RELATIONAL_OBSERVATION_SYMBOLIC_FEEDBACK_SYNTHESIS.md) supplies exact
source reconstruction charts when that stronger object is
needed. The finite type chart and the padding section here
have the distinct weaker purpose specified above.

[Sparse Literal History Transport §§69.1--69.4, (SLH.69.17)
and Theorem 74.4](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) already supply unrestricted-depth bounded
literal-task methods, the finite unit-call minimax and
whole-row prefix checking.
[Native Signed Feasibility §§7.1--7.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md) supplies finite protocol unrolling and
supplied-box checking. Those mature methods are reused;
the ordinary new composition is the actual one-image
root admissibility, whole predecessor factorization and
the same-$r,q$ joint supplement transfer. The finite
criterion consumes precisely that correspondence.

Decision trees and query geometry are mature context,
with the bounded attribution to Robert Nowak,
*The Geometry of Generalized Binary Search*,
[arXiv:0910.4397v5](https://arxiv.org/abs/0910.4397v5),
§V.A, printed p.14 / PDF p.15, already stated in
Mathematical citation 9.7. That passage compares
restricted singleton testing and richer dyadic geometry;
it supplies neither the native image chart nor this
acquired/exported predecessor correspondence. This
section is a repo-derived ordinary mathematical package,
with no literature-priority or Lean-kernel claim.

The same-budget invariant is joint deterministic
existence. It preserves neither an arbitrary fixed
advice map pointwise, all native behavior, complete
traces, arbitrary total controller states, word lengths,
workspace, local computation time nor physical costs.
In particular a padded representative does not supply
future replies for an arbitrary other source. The
finite criterion constructs a new allowed protocol
rather than effectively transform arbitrary promised
program text.

Complete acquisition, actual export, the full access
cut, authentication, stationary reading and the lawful
common entry are supplied premises of Theorem 10.8.
The producer uses acquired roots to compute the finite
coloring, actual export carries that value across the
cut, and the entry and isolation premises make each
reader segment determined by its payload and replies.
Source-dependent discarded material must
remain inaccessible or factor through the declared
payload; physical erasure is not asserted. Initial
full traversal, local finite comparisons, row storage,
code storage, installation, permissions, address
transmission and outputs remain separate charges.
Zero fresh calls after the cut is not zero acquisition.

The native alpha-recut volume §12 owns its relative
epoch result from acquired rows along one actual
history. No relative-time statement is added here.
The remaining controller-memory programme must
separately analyze the cost of its whole common
controller and retained state. Root-protocol
feasibility alone is not that state-count theorem
and does not complete that continuing programme.

## 追加锚（本行以下为增补区）
## 11. Total stationary Moore states on the repeated-partner inverse fiber

### 11.1 The counted controller and its complete entry record

**Definition 11.1 (stationary finite controller contract).** Use exactly
$\mathcal U_*$, $F$, $P$, $R_*$, the six classes and the four complete
predecessor alternatives of Definition 9.1 and Proposition 9.3, together
with alternative zero. The suppliers are Definitions 9.1, Assumption 9.2,
Propositions 9.3--9.4, Theorem 9.5 and Mathematical citation 9.7 at the
immutable revision
[a56175a1ce5884e0aa6f7e4ff3109dfaaecdd4a3](https://github.com/the-omega-institute/trureturing/blob/a56175a1ce5884e0aa6f7e4ff3109dfaaecdd4a3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#9-repeated-partners-on-a-complete-depth-three-one-image-fiber).
In particular every finite native origin in that actual inverse fiber
is allowed, exactly one authenticated update has occurred, and all fresh
reads concern its stationary current tree $t=\rho u$. Acquisition, actual
export, the complete access cut and lawful common entry are precisely
the supplied premises of Assumption 9.2.

A controller has a finite disjoint state set $\mathcal K=Q\sqcup H$,
where $Q$ consists of running states and $H$ of halting states. Its
source-independent tables are

$$
\begin{aligned}
\operatorname{addr}&:Q\longrightarrow\{L,R\}^*,\\
\operatorname{next}&:Q\times
 \{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}
 \longrightarrow\mathcal K,\\
\operatorname{out}&:H\longrightarrow\mathcal R_P,\\
\iota&:S\longrightarrow\mathcal K.
\end{aligned}
\tag{NBP.11.1}
$$

Here $\mathcal R_P$ denotes complete native rows at $P$. A producer
computes a finite-valued supplement $\sigma$ from the genuinely acquired
current data and actually exports it. The conditional realized alphabet
is $S=\sigma[\mathcal U_*]$, with $|S|\le r$. The entry state is
$\iota(\sigma(u))$. This state is the entire mutable accessible state;
there is no residual payload, address register, reply register, history,
phase, clock, archive, source-dependent table selection or external
output decoder. At $k\in Q$ exactly one native call is made at the fixed
address $\operatorname{addr}(k)$, and its actual four-reply result $z$
changes the state to $\operatorname{next}(k,z)$. At $k\in H$ the controller
stops and returns the fixed whole row $\operatorname{out}(k)$. Every call
counts, including repeats, deep and absent queries. Every running and
halting state, including an unused state, contributes to
$K=|\mathcal K|$. Halting needs no further native call.

The interpretation of $\iota$ must respect Assumption 9.2's recoverable
complete entry record. In a literal realization with the original
supplement still recoverable from the entry state, $\iota$ is injective
on $S$. For joint encoder/controller optimization a possibly merging
initial map is normalized before the cut: the producer instead computes
and actually exports $\tau(u)=\iota(\sigma(u))$. This uses at most $r$
values and the same acquired data. The declared supplement is then
$\tau$, the initial map is its inclusion into $\mathcal K$, and the
supplement is recoverable from that state. The public $P,R_*$ and common
tables remain fixed. Lawful entry and the complete cut are supplied for
this actual export. No later access to the old $\sigma$ is permitted.
Thus merging does not silently preserve a second accessible field or
claim a result for a fixed arbitrary encoder.

Let $K_{\min}(r,q)$ be the least $K$ among these jointly chosen acquired
encoders and controllers which return $F(u)$ for every
$u\in\mathcal U_*$, with at most $q$ calls on each run. Set
$K_{\min}(r,q)=+\infty$ when none exists. Throughout $r\ge1$ and $q\ge0$
are integers and both budgets are upper bounds. The contract optimizes
only abstract total state cardinality and raw native calls. The addresses
and fixed tables in (NBP.11.1), their representations, acquisition,
export, computation and physical realization have separate prices.

### 11.2 The actual five-source state and capacity bounds

**Proposition 11.2 (bounds without a tree-shaped controller assumption).**
Every successful controller of Definition 11.1 satisfies

$$
r2^q\ge5,\qquad K\ge5,\qquad K\ge10-r.
\tag{NBP.11.2}
$$

**Proof.** Such a controller is an allowed reader in Assumption 9.2.
Theorem 9.5 therefore gives the first inequality on the original full
fiber, with the actual exported alphabet and all native invocations
counted. This is reuse of that joint capacity bound, not an assertion
that every encoder with the same alphabet size performs equally well.

For the state bounds restrict the one controller, with its actual
initial states, to the five actual sources $u_0,\ldots,u_4$ of
(NBP.9.6). Their correct complete rows $R_0,\ldots,R_4$ are distinct.
Their five terminal states must consequently be different. In particular
$K\ge5$, even if some initial states are already halting states.

Form the directed union graph of the five finite actual runs. Let $n$
be its number of running vertices, and let $I$ be its set of distinct
initial vertices, with $m=|I|\le r$. There are exactly five terminal
vertices in this union. Proposition 9.4 applies to every state's fixed
address, however deep or absent, so at most two different replies occur
there on these sources. Each running vertex has at most two distinct
successor edges in the union graph. Hence its number $e$ of edges obeys
$e\le2n$.

Every vertex is reachable from $I$ along an actual run prefix. Choosing
one incoming edge for each vertex outside $I$ along a shortest path from
$I$ gives a rooted spanning forest and therefore

$$
n+5-m\le e\le2n,
\qquad K\ge n+5\ge10-m\ge10-r.
\tag{NBP.11.3}
$$

The rooted spanning-forest count is the existing finite-control graph
method used in Transport--Memory Completion Theorem 66.3, here applied
to the five actual binary-response witnesses. It requires neither a
binary native interface on the full fiber nor an acyclic union graph.
Converging edges, cycles shared across different runs, repeated queries,
early halts and initial halting vertices are all included. Other states
used only on other origins, and unused states, only increase $K$.
The five halts issue the five complete rows; an uncharged retained label
cannot supply their missing output distinction. $\square$

### 11.3 Six simultaneous finite witnesses for the three-call obstruction

**Proposition 11.3 (two zero targets with opposite beta placements).**
Keep $A,C,D_1,\ldots,D_4$ from (NBP.9.6), all distinct branch images.
Let

$$
Z=\{0_a,0_c,1,2,3,4\},\qquad
G_a=\{0_a,1,2\},\qquad G_c=\{0_c,3,4\}.
\tag{NBP.11.4}
$$

Define six finite tuples by

$$
\begin{aligned}
x_a^{(z)}&=
 \begin{cases}\beta,&z\in G_a,\\ A,&z\in G_c,\end{cases}\\
x_c^{(z)}&=
 \begin{cases}C,&z\in G_a,\\ \beta,&z\in G_c,\end{cases}\\
x_{b_j}^{(z)}&=
 \begin{cases}\alpha,&z=j,\\D_j,&z\ne j,\end{cases}
 \qquad(1\le j\le4).
\end{aligned}
\tag{NBP.11.5}
$$

Then $t_z=\mathscr S(x^{(z)})$ is an actual current image and
$u_z=\delta(t_z)$ belongs to the full original $\mathcal U_*$. Their
required outputs are

$$
F(u_{0_a})=F(u_{0_c})=R_0,\qquad F(u_j)=R_j\quad(1\le j\le4).
\tag{NBP.11.6}
$$

On these six simultaneous fixed actual sources, every finite address
has either constant reply, two replies partitioning $G_a\mid G_c$, or
two replies isolating exactly one $j\in\{1,2,3,4\}$. More precisely:

| Address location | Possible nonconstant reply partition on $Z$ |
| --- | --- |
| At length less than three | None |
| In either occurrence cone of $a$ | $G_a\mid G_c$ |
| In either occurrence cone of $c$ | $G_a\mid G_c$ |
| In the occurrence cone of $b_j$ | $\{j\}\mid(Z\setminus\{j\})$ |

**Proof.** In every tuple exactly one of $a,c$ is beta, the other is
its fixed branch image, and the remaining four coordinates are distinct
branch images except for the possible one alpha at $b_j$. The six
coordinates are pairwise distinct. For $0_a$ and $0_c$ all are images,
and for $j$ the alpha has exactly its forced beta partner. Proposition
9.3 supplies the actual finite inverse and the stated complete outputs.
All six current trees and origins are fixed at once; no run changes its
source in response to a query.

For every address of length at least three write it uniquely as $pw$
with $p\in P$. The actual occurrence identity (NBP.9.7) gives
$r_{t_z}(pw)=r_{x_{[p]}^{(z)}}(w)$. In an $a$ cone the only subtree
values are beta and $A$, constant on the two groups; in a $c$ cone they
are $C$ and beta, constant on the same two groups. In a $b_j$ cone the
only subtree values are alpha at $j$ and $D_j$ otherwise. Evaluating
these two fixed finite trees at any suffix gives either equal replies
or the indicated partition. A suffix may continue beyond a leaf or
beyond the finite subtree; absent is the ordinary native reply and
changes none of this argument. Shorter addresses are common skeleton
branches. One address enters one occurrence cone even when a class
occurs twice. Thus the table covers all finite native addresses without
restricting the query menu or replacing actual replies by an extra
experiment port. $\square$

**Theorem 11.4 (constant advice and three calls require ten states).**
For $r=1$ and $q=3$, every successful controller has at least five
running states and at least five halting states. In particular
$K\ge10$.

**Proof.** Restrict it to the six actual sources of Proposition 11.3.
Constant advice gives one common initial state. Five different required
outputs exclude an initial halt. At any later state, the fixed address
has at most two replies on these six sources. Consequently one remaining
call can distinguish at most two different required outputs, and two
remaining calls at most four, including early halts. These elementary
binary-depth bounds are the same decision-tree capacity supplier used
in Theorem 9.5, applied only to these actual runs.

The first call cannot have constant reply: that would leave all five
outputs for two calls. It also cannot isolate a single positive index
$j$. On the other reply its remaining candidates would be
$Z\setminus\{j\}$, with four distinct required outputs. Any possible
second call on that set has one of the following forms by Proposition
11.3. A constant query leaves four outputs for one call. A singleton
query for another positive index leaves three outputs on its other
reply. A group query leaves the opposite group, the one not containing
$j$, intact, with its three different outputs $R_0$ and its two positive
rows. Each case leaves at least three outputs for one call and is
impossible. Querying the removed singleton is constant on the remaining
set, so is included. Halting before the second call cannot resolve its
four outputs either.

Thus the first call separates $G_a$ from $G_c$ and its running state has
an address in an $a$ or $c$ occurrence cone. Consider its $G_a$ reply.
There are exactly the three outputs $R_0,R_1,R_2$ and at most two calls
left. Both partner-cone queries are now constant, as are skeleton queries
and singleton queries for $3$ or $4$. The second call must therefore be
a nonconstant query in a $b_1$ or $b_2$ cone. It isolates that positive
index. On the other reply the remaining two actual sources are $0_a$
and the other index in $\{1,2\}$. Their only nonconstant queries are in
the other right-class cone, so the third call must query that cone.
Both $b_1$ and $b_2$ cones are therefore queried on actual runs.

The identical argument on $G_c$ forces actual queries in both $b_3$ and
$b_4$ cones. These four right-class cones and the partner cone of the
first call are disjoint address locations. Each running state has one
fixed address, so at least five different running states are necessary.
No merging of reply histories can change that address requirement. The
five different whole outputs require five different halting states by
(NBP.11.6), disjoint from the running states. Early stopping on an
isolated positive index is allowed in the argument; convergence, cycles
in a union of runs and unused states cannot remove the five necessary
address states. Hence $K\ge10$.

This is a direct obstruction on the native finite sources and their
occurrence cones. It does not use a root simulation, padding reduction,
or any state-count-preserving consequence of Theorem 10.8. $\square$

### 11.4 Matching controllers on every actual origin

**Proposition 11.5 (full-fiber upper controllers).** The following exact
numbers of states and worst-case calls are simultaneously attainable.
Each listed initial distinction is actually exported from the acquired
data of Assumption 9.2.

| Exported capacity used | Maximum calls | Running states | Halting states | Total states |
| --- | --- | --- | --- | --- |
| $1$ | $3$ | $5$ | $5$ | $10$ |
| $1$ | $4$ | $4$ | $5$ | $9$ |
| $2$ | $2$ | $3$ | $5$ | $8$ |
| $3$ | $1$ | $2$ | $5$ | $7$ |
| $4$ | $1$ | $1$ | $5$ | $6$ |
| $5$ | $0$ | $0$ | $5$ | $5$ |

**Proof.** Proposition 9.3 makes the acquired right-class terms determine
$h\in\{0,1,2,3,4\}$, with $h=j$ exactly when $x_{b_j}=\alpha$ and
$h=0$ when no right-class term is alpha. As in Theorem 9.5, this is a
pre-cut computation on genuinely acquired finite values. Only the stated
block index is exported; no term, target marker or previous reply remains
accessible in addition to the resulting initial state.

In every controller below there are exactly five halts
$H_0,\ldots,H_4$, with $\operatorname{out}(H_j)=R_j$. These are the
complete repaired rows of Proposition 9.3: $H_0$ returns $R_*$, while
$H_j$ for $j>0$ returns the exterior with precisely the pair at $q_j$
replaced by one concrete beta, its restricted occurrence partition with
recomputed canonical names, every retained disequality and the resulting
absent-cut guards. The surviving occurrence of the repeated partner
remains a hole. Thus $H_j$ is not a label output followed by an uncharged
source-dependent decoding step.

Write $p_j=q_jR$ for the four right-class root addresses and $p_a=LLL$
for a root of $a$. A state named $B_j$ always queries $p_j$. In the
transition descriptions, an alpha reply takes the stated alpha edge;
every other reply takes the non-alpha edge. This defines the table for
all four native replies, including formally unreachable replies. Every
$p_j$ is reached on the entire fiber, and Proposition 9.3 shows that the
alpha edge is taken exactly for $h=j$.

For the first row of the table, export one constant value and start at
an additional running state $A_0$ querying $p_a$. Define the transitions
by

$$
\begin{array}{c|c|c}
\text{state}&\text{reply condition}&\text{successor}\\ \hline
 A_0&\beta&B_1\\
 A_0&\mathsf{branch}&B_3\\
 A_0&\alpha\text{ or }\mathsf{absent}&H_0\\
 B_1&\alpha&H_1\\
 B_1&\text{non-alpha}&B_2\\
 B_2&\alpha&H_2\\
 B_2&\text{non-alpha}&H_0\\
 B_3&\alpha&H_3\\
 B_3&\text{non-alpha}&B_4\\
 B_4&\alpha&H_4\\
 B_4&\text{non-alpha}&H_0
\end{array}
\tag{NBP.11.7}
$$

The $A_0$ alpha and absent edges never occur on the actual domain.
If $x_a=\beta$, the target can be only $0,1,2$: a positive target $3$
or $4$ would also force $x_c=\beta$, violating the retained disequality.
If $x_a$ is a branch, the target can be only $0,3,4$, since $1,2$ force
$x_a=\beta$. The subsequent two right-class tests therefore give the
whole correct target in at most three calls. There are five running
states and five halts, and both group branches and all halts are attained
by actual origins.

For the second row, export one constant value and start at $B_1$.
Use four running states $B_1,\ldots,B_4$; $B_j$ takes its alpha edge to
$H_j$, and its non-alpha edge to $B_{j+1}$ for $j<4$ or to $H_0$ for
$j=4$. This checks for the unique possible alpha among all four right
classes, with at most four calls and nine total states.

For the third row, export the block in
$\{0,1,2\}\mid\{3,4\}$ and initialize respectively at $B_1$ or $B_3$.
Use only $B_1,B_2,B_3$. Their alpha edges go to their corresponding
halts. Their non-alpha edges are respectively $B_2,H_0,H_4$.
These two initial states, three running states and five halts give
maximum two calls and total eight states.

For the fourth row, export the block in
$\{0\}\mid\{1,2\}\mid\{3,4\}$ and initialize at $H_0,B_1,B_3$,
respectively. The two running states have alpha edges $H_1,H_3$ and
non-alpha edges $H_2,H_4$, respectively. This gives seven total states
and at most one call, including a genuine zero-call initial halt.

For the fifth row, export the block in
$\{0\}\mid\{1\}\mid\{2\}\mid\{3,4\}$ and initialize at
$H_0,H_1,H_2,B_3$, respectively. The single running state has alpha edge
$H_3$ and non-alpha edge $H_4$. This gives six states and at most one
call. For the last row export $h$ itself and initialize at $H_h$. Only
the five halts are needed, with no fresh call.

Every block in these constructions is nonempty on the full fiber, by
the actual witnesses of Proposition 9.3. Every named state is reached
on some actual origin. The maximum call count in the constant-export
constructions is attained on every target-zero source; for the other
positive-call rows it is attained in a non-singleton block. Their
initial distinctions have exactly the alphabet sizes in the table and
satisfy Definition 11.1's complete-entry normalization.

For explicit coverage of the target-zero cases, all six class values
are images and are pairwise distinct. Therefore beta can occur in at
most one of the six classes: it can be at $a$, at $c$, at any $b_j$, or
nowhere. Every one of these placements is attained, by replacing the
chosen coordinate in a tuple of six distinct branch orbit images by
beta, or leaving all six as branches. Proposition 9.3 supplies the
actual finite inverse in each case. If beta is at $a$, (NBP.11.7) takes
its first branch and then two non-alpha edges to $H_0$. In all other
zero placements it takes its branch-reply edge and then two non-alpha
edges to $H_0$, even when the tested right class itself is beta. The
sequential four-test controller also returns $H_0$ in all these cases.
The exported-block controllers either start at $H_0$ or retain zero in
the first block and test its right classes. No claim that a partner
query is a target-only group test on the full fiber is required. These
arguments also cover every other branch filling, regardless of its
size or internal alpha/beta distribution. $\square$

### 11.5 Exact frontier and resource interpretation

**Theorem 11.6 (minimum total-state frontier on the full actual fiber).**
Under Definition 11.1, for every integer $r\ge1,q\ge0$,

$$
K_{\min}(r,q)=
\begin{cases}
+\infty,&r2^q<5,\\
10,&(r,q)=(1,3),\\
\max\{5,10-r\},&r2^q\ge5\text{ and }(r,q)\ne(1,3).
\end{cases}
\tag{NBP.11.8}
$$

Equivalently the finite part is the following table; a dash means no
successful controller.

| Advice capacity $r$ | $q=0$ | $q=1$ | $q=2$ | $q=3$ | $q\ge4$ |
| --- | --- | --- | --- | --- | --- |
| $1$ | -- | -- | -- | $10$ | $9$ |
| $2$ | -- | -- | $8$ | $8$ | $8$ |
| $3$ | -- | $7$ | $7$ | $7$ | $7$ |
| $4$ | -- | $6$ | $6$ | $6$ | $6$ |
| $r\ge5$ | $5$ | $5$ | $5$ | $5$ | $5$ |

In particular nine total abstract states cannot solve the task in three
calls with constant advice, while ten can; nine suffice with four calls.

**Proof.** Proposition 11.2 rules out every $r2^q<5$ and gives
$K\ge\max\{5,10-r\}$ in all feasible cases. Theorem 11.4 strengthens
this to ten at $(1,3)$. Proposition 11.5 gives ten there, nine for
$r=1,q\ge4$, eight for $r=2,q\ge2$, seven for $r=3,q\ge1$, six for
$r=4,q\ge1$, and five for $r\ge5,q\ge0$. These exhaust the integer
feasible cases. A controller using fewer than $r$ values or fewer than
$q$ calls satisfies the upper-bound contract; no dummy invocations or
extra initial distinctions are inserted. Extra unused states are
charged and cannot defeat either lower proof. If a larger exact state
cardinality is separately prescribed, unused fixed halting states can
be adjoined without changing any actual run. $\square$

**Proposition 11.7 (the two optimized resources and their limits).**
The frontier (NBP.11.8) charges the complete changing finite control
state, including phase and reply memory, and every fixed whole-row
halting distinction. It does not identify exported capacity with
running memory or with physical storage. In particular the nine-state
and ten-state constant-advice controllers both require four bits in a
fixed-width injective binary state encoding, although their total state
cardinalities and three-call feasibility differ.

**Proof.** All later action choices and outputs in (NBP.11.1) depend only
on the current state and the actual reply. A separately remembered
phase, payload or response which changes a future action would be an
additional accessible mutable distinction and would have to be included
in $\mathcal K$. Distinct fixed complete outputs require distinct halt
states, as used in both lower proofs. The initial export merely selects
at most $r$ states; it need not remain separately accessible thereafter.
For example the constant export has one value while the three-call
controller visits different partner and right-test states. Conversely
five exported values can initialize five halts with no running states.
These are different counted objects.

A binary fixed-width representation of a set of size $K$ needs and
admits $\lceil\log_2 K\rceil$ bits. Since $8<9<10\le16$, both stated
controllers have width four under this representation convention.
This observation counts neither the fixed address/action/transition/
output tables nor the representation and production of their full row
outputs. The supplied entry, authentication, producer acquisition,
finite comparisons, actual export, access cut, installation, local
computation, address transmission and physical service retain their
separate costs. An image inverse used to construct a proof witness is
not a native inverse operation. No further update is available.

Thus (NBP.11.8) settles the history-memory question under this explicit
stationary finite Moore restriction: every accessible changing
source-dependent distinction is included in its finite state. An
arbitrary program with unbounded workspace or a computed address has a
different contract; identifying its total configurations with finitely
many states of (NBP.11.1) requires a separate proof. Neither nine versus
ten states nor three versus four native calls is a universal physical
memory or time equivalence. $\square$

**Mathematical citation 11.8 (suppliers, mature methods and exact delta).**
The one-image grammar, injective inverse, actual row fiber and
occurrence-sensitive repair are the suppliers already cited in
Definitions 1.1--1.2, Theorems 2.2 and 3.2, and Proposition 9.3.
Assumption 9.2 supplies acquired/exported entry rather than deriving it
from a row identity. Propositions 9.3--9.4 supply the fixed five actual
witnesses and their all-address binary bridge, and Theorem 9.5 supplies
the joint capacity frontier and the full-fiber root-test strategies.
The same-$r,q$ existence transfer of §10 supplies no state-cardinality
invariant and is not a premise of either state lower bound here.

Finite Moore state/output conventions are classical; see Edward F.
Moore, *Gedanken-Experiments on Sequential Machines*, in *Automata
Studies* (AM-34), pp.129--153,
[DOI:10.1515/9781400882618-006](https://doi.org/10.1515/9781400882618-006).
The rooted reachable-graph edge count is reused in the form of
[Transport--Memory Completion Theorem 66.3](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#TM66-T3),
with its domain and response hypotheses replaced by the actual five
witnesses in Proposition 11.2, rather than importing its numerical
source-specific conclusion. Adaptive query geometry and binary-depth
counting are the mature methods attributed in Mathematical citation
9.7, including Nowak's *The Geometry of Generalized Binary Search*,
[arXiv:0910.4397v5, §V.A](https://arxiv.org/abs/0910.4397v5).
Those methods supply neither the six sources of Proposition 11.3 nor
its native-cone obstruction. The repo-derived numerical delta is the
full-fiber total-state charging and the exceptional three-call lower
bound, together with the matching common finite controllers. It is an
ordinary mathematical deduction, with no literature-priority claim.
Quantum terminal-rank minima and stochastic hidden/visible-memory minima
concern different sources, operations, targets and resources; none is a
supplier for (NBP.11.8).

## 追加锚（本行以下为增补区）

## 12. Exact joint record, total Moore-state and call transfer on every full fiber

### 12.1 The unchanged domain and the two counted shared tables

**Definition 12.1 (full-fiber stationary Moore feasibility).** Fix any
$P,R_*$ of Definition 10.1 with $\mathcal U_*\ne\varnothing$. Keep
exactly its actual finite origins, injective class valuations
$\mathcal X_*$, complete exterior, reached classes $D$ and representative
occurrences $p_d$. Keep the attained chart $\Theta_*$ of Proposition 10.2
and the whole predecessor target $G_*$ of Theorem 10.4. Equivalently,
write $\Phi_C=\Theta_*$ and $G_C=G_*$ for the finite attained class-root
task. No source-size, depth, intrinsic-rank or selected-witness promise
is added to $\mathcal U_*$. The source and update remain the finite
ordered $\alpha/\beta$ trees and homomorphic $\rho$ of Definition 1.1.

Use the acquired/exported, complete-access-cut, authenticated one-update,
lawful-common-entry and stationary-reading premises of Assumption 10.6.
Impose the finite Moore restriction of Definition 11.1 on this general
row: there is one common installed finite set
$\mathcal K=Q\sqcup Z$ of running and halting states and fixed tables

$$
\begin{aligned}
\operatorname{addr}&:Q\longrightarrow\{L,R\}^*,\\
\operatorname{next}&:Q\times\mathcal A\longrightarrow\mathcal K,
 &\mathcal A&=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\},\\
\operatorname{out}&:Z\longrightarrow\mathcal R_P.
\end{aligned}
\tag{NBP.12.1}
$$

At a running state $a$ one invocation reads the actual stationary
$t=\rho u$ at $\operatorname{addr}(a)$; its reply $z$ sets the next
state to $\operatorname{next}(a,z)$. A halting state returns its fixed
entire row $\operatorname{out}(a)$ without a call. All installed states
count, including unused states and distinct halts with equal outputs.
There is one fixed finite address per running state. Replies, repeated
queries, exterior queries, arbitrarily deep queries and absence all
obey the original native contract and each invocation counts.

The actual pre-cut export initializes the current state. After entry,
that state is the entire accessible source-dependent controller memory:
there is no separate advice register, pointer, phase, clock, trace,
archive, decoder, variable address or source-dependent table selection.
The row, cut and installed tables are common source-independent data.
In particular every halting output is already a complete predecessor
row, rather than a label requiring a source-bearing output decoder.

Complete-entry recoverability is retained as in Assumptions 9.2 and
10.6 and Definition 11.1. If an original export $\sigma$ and entry map
$\iota$ merge values, the admissible joint normalization is the actual
pre-cut computation and export

$$
\tau(u)=\iota(\sigma(u))\in\mathcal K.
\tag{NBP.12.2}
$$

The declared exported value is then this initial-state code, its entry
map is inclusion, and it is recoverable from the initial state. Its
actual range has at most $|\sigma[\mathcal U_*]|$ elements. The producer
uses its acquired data, actually exports $\tau$ before the access cut,
and uses the supplied lawful entry for that export. This is a changed
encoder when $\iota$ merges; it does not retain the old $\sigma$ as an
extra accessible field. It grants no pointwise statement for a fixed
arbitrary encoder. Below the normalized initialization is written
$\tau:\mathcal U_*\to\mathcal K$ and must be so acquired and exported.

For integers $r\ge1,K\ge1,q\ge0$, let
$\mathsf{MooreInvFeas}_*(r,K,q)$ mean joint existence of such an actual
export and table with $|\tau[\mathcal U_*]|\le r$,
$|\mathcal K|\le K$, and at most $q$ native invocations on each origin,
terminating with $F(u)=R_P(u)$ on every $u\in\mathcal U_*$. The three
budgets are upper bounds. Address representation, installed tables,
fixed whole-output storage, acquisition, export and physical services
have separate prices; $K$ counts states, not all physical memory.

**Definition 12.2 (attained class-root Moore feasibility).** The root
task has input $\theta\in\Theta_*\ne\varnothing$ and entire target
$G_*(\theta)$. It has one finite shared table on
$\mathcal K=Q\sqcup Z$, with the same fixed complete halting outputs
and reply-only transition rule as (NBP.12.1), except that

$$
\operatorname{coord}:Q\longrightarrow D
\tag{NBP.12.3}
$$

labels each running state by one actual hidden-class root coordinate.
One call at that state returns $\theta(\operatorname{coord}(a))$;
$\mathsf{br}$ in the chart denotes the native $\mathsf{branch}$ reply.
All coordinates are reached, so absence is impossible, but the fourth
transition entry may be filled with an arbitrary existing state. Every
invocation, including a repeated coordinate, costs one. There is no
constant-query port or free control step. If $D=\varnothing$, the
coordinate map forces $Q=\varnothing$.

A finite coloring $c:\Theta_*\to\mathcal K$ with
$|c[\Theta_*]|\le r$ specifies the complete exported initial-state
code; only that current state remains accessible after entry. No free
color register is retained. Let $\mathsf{MooreRootFeas}_*(r,K,q)$ mean
joint existence of this coloring and table with $|\mathcal K|\le K$,
terminating in at most $q$ calls with $G_*(\theta)$ for every attained
$\theta$. Installed running and halting states, including unused ones,
are charged exactly as in Definition 12.1. This is a finite comparison
task, not an extra observation port supplied to the original register.

### 12.2 A correspondence on shared states, without history unrolling

**Theorem 12.3 (paid root recoding of an arbitrary installed native
state graph).** Suppose $D\ne\varnothing$ and a table and normalized
actual export witness $\mathsf{MooreInvFeas}_*(r,K,q)$. There are one
actual origin $u^\theta\in\mathcal U_*$ for every
$\theta\in\Theta_*$ and a root table with exactly the same installed
state set, running/halting partition and halting outputs. Its coloring
uses at most the original number of exported initial-state values.
For each $\theta$, its entire state path and call count equal those of
the native table on that one fixed $u^\theta$. In particular it
witnesses $\mathsf{MooreRootFeas}_*(r,K,q)$, including shared states,
converging transitions and unused installed states.

**Proof.** The finite installed native table, rather than its execution
histories, supplies the finite address menu. Put

$$
L=\max\bigl(\{0\}\cup
             \{|\operatorname{addr}(a)|:a\in Q\}\bigr).
\tag{NBP.12.4}
$$

This includes unused running states and all arbitrarily long words of
this particular table. It restricts no allowed comparator and no actual
source. Proposition 10.5 at this $L$ supplies simultaneously the actual
finite valuations $x^\theta$, current images
$t^\theta=\mathscr F_*(x^\theta)=\rho u^\theta$ and origins
$u^\theta\in\mathcal U_*$. Their branch classes have minimum leaf
depth greater than $L$, their repeated occurrences share their values,
and every class disequality and exterior absence guard is retained.
They realize every attained $\theta$, and
$F(u^\theta)=G_*(\theta)$ by Theorem 10.4.

For each installed native word $v$, traverse the complete fixed
exterior. If it never enters a hole, its reply $b_v\in\mathcal A$
is constant on every $t^\theta$. This includes the root when visible,
concrete exterior constructors, blocked cut cones, and extensions of
concrete leaves. If it first enters $p\in H$, write $v=pw$ and
$d=[p]$. Proposition 10.5 gives the following single state-local
response function on reached root replies:

$$
h_v(z)=
\begin{cases}
z,&w=\varepsilon,\\
\mathsf{absent},&w\ne\varepsilon,\quad z\in\{\alpha,\beta\},\\
\mathsf{branch},&w\ne\varepsilon,\quad z=\mathsf{branch}.
\end{cases}
\tag{NBP.12.5}
$$

Thus $r_{t^\theta}(v)=h_v(\theta(d))$. The same class name is used
whichever occurrence cone is entered. At a nonempty suffix, both leaf
roots give absence and every padded branch root gives a reached branch;
no information from its deeper finite shape is used.

Choose once a genuine $d_0\in D$. For a constant word, set
$j_v=d_0$ and $h_v(z)=b_v$ for every $z\in\mathcal A$. For a word
entering a hole, set $j_v=d$ and extend (NBP.12.5) arbitrarily to the
unreachable argument $\mathsf{absent}$. Consequently every installed
word, constant or variable, satisfies

$$
r_{t^\theta}(v)=h_v(\theta(j_v))
\quad(\theta\in\Theta_*).
\tag{NBP.12.6}
$$

Install the root table on the very same $Q\sqcup Z$ by

$$
\begin{aligned}
\operatorname{coord}'(a)&=j_{\operatorname{addr}(a)},\\
\operatorname{next}'(a,z)&=
 \operatorname{next}\bigl(a,h_{\operatorname{addr}(a)}(z)\bigr),\\
\operatorname{out}'&=\operatorname{out},\qquad
c(\theta)=\tau(u^\theta).
\end{aligned}
\tag{NBP.12.7}
$$

The coloring is a finite table into the original installed states and
$|c[\Theta_*]|\le|\tau[\mathcal U_*]|\le r$. It does not assert that
$\tau$ is constant on the root-type fibers. Its declared value is the
initial-state code itself, so initialization has no extra retained
field or subsequent decoding phase.

Fix $\theta$. Both executions start in $\tau(u^\theta)$. Whenever
their common current state is running, (NBP.12.6) and (NBP.12.7) make
the next states equal, with exactly one counted invocation on each
side. At a constant word the root reader really queries $d_0$ and
ignores its reply through the constant function $h_v$. That invocation
is charged; it is neither an artificial native response nor a free
transition. At a halting state the outputs agree. Induction along this
one actual source's execution proves the asserted state path and call
count equality, termination in at most $q$ calls, and whole output
$F(u^\theta)=G_*(\theta)$.

The recoding depends only on the installed state, not on which history
reached it. Hence the same next-state rule applies when different
sources converge at a state; repeated visits by different sources need
no copies, and unused states remain installed and counted. No tree
unrolling, cloned state, retained clock or new control phase occurs.
The actual representatives establish necessity from a full-fiber
native solution; they do not become a restriction of that solution's
domain. $\square$

**Theorem 12.4 (exact joint three-budget feasibility transfer).** Under
the supplied operational premises in Definition 12.1, for every
nonempty full actual one-image row fiber and every integer
$r\ge1,K\ge1,q\ge0$,

$$
\mathsf{MooreInvFeas}_*(r,K,q)
\quad\Longleftrightarrow\quad
\mathsf{MooreRootFeas}_*(r,K,q).
\tag{NBP.12.8}
$$

The same upper budgets charge actual exported initial distinctions,
all installed running and halting states, and every invocation. The
native side retains every actual finite origin and every legal finite
native address.

**Proof.** First suppose $D\ne\varnothing$. The native-to-root
direction is Theorem 12.3. For the converse, take a root coloring and
shared table satisfying Definition 12.2. Install the same state set,
partition, transition table and whole halting outputs on the native
register, replacing each coordinate $d$ by the actual native address
$p_d$. Every $p_d$ is reached on every source of the fixed row fiber.
For any actual valuation $x\in\mathcal X_*$ its reply is exactly
$\theta_x(d)$; the absent transition entry is never used at these
addresses. No bound on hidden branch depth or shape is needed.

The producer inspects the roots of its actually acquired class values,
computes $\theta_x\in\Theta_*$, and computes the finite-table value
$c(\theta_x)$. It actually exports this initial-state code before the
complete access cut and uses the supplied common lawful entry. Local
inspection of acquired terms is not a fresh native call. The export
has at most $r$ values and is recoverable from the initial state.
Proposition 10.2 makes every type attained, so its actual code range
is exactly $c[\Theta_*]$. Nothing else from acquisition is available
after entry.

For this arbitrary actual origin, induction on the current state makes
the native run identical to the root run on $\theta_x$, with one native
invocation for each root invocation and the same halting state. Thus
the state cardinality is unchanged, the call bound is $q$, and the
output is $G_*(\theta_x)=F(u_x)$ by Theorem 10.4. In particular it
includes the inverse exterior, canonical restricted partition with
all equalities and disequalities, repeated occurrences and every
predecessor absence guard. The same installed table works for all
actual origins; the necessity witnesses are not used for this direction.

If $D=\varnothing$, Proposition 10.2 gives the singleton chart
containing the empty type. The complete current tree is the exterior,
and its unique actual predecessor and entire predecessor row are fixed.
On both sides install one halting state with that row as its fixed
output and export its one initial-state code. This uses one state, one
actual value and zero calls, within every stated $r,K,q$. It asks no
nonexistent coordinate and makes no dummy native invocation. Therefore
both sides are feasible, proving (NBP.12.8) also for zero classes.
$\square$

**Proposition 12.5 (stationary per-source paths and cyclic union graphs).**
Every terminating run of either counted table visits each running
state at most once. The graph obtained by taking the union of paths
from different actual sources or different attained types need not be
acyclic. The transfers of Theorems 12.3--12.4 apply to this shared graph
without an acyclicity premise.

**Proof.** On a fixed stationary source, the reply to the one address
of a given state is fixed. If the same running state were revisited,
the deterministic suffix from it would repeat forever, contradicting
termination. The root task has the same property for a fixed $\theta$.
This argument fixes the source; it does not make all transitions from
a running state use the same successor across different sources.

For an explicit actual-fiber example, take $P=\{\varepsilon\}$ and
its one-hole current row. There is one class $d$, its attained types
are $\beta$ and $\mathsf{branch}$, and its whole predecessor row is
constant by Corollary 10.10. Install running states $a,b$, both querying
$d$, and a halt $h$ carrying that fixed row. Put
$\operatorname{next}(a,\beta)=b$,
$\operatorname{next}(b,\beta)=h$,
$\operatorname{next}(b,\mathsf{branch})=a$ and
$\operatorname{next}(a,\mathsf{branch})=h$; let the other replies go to
$h$. Export initial state $a$ on type $\beta$ and $b$ on type
$\mathsf{branch}$. This is an actual acquired two-value initialization.
The paths are $a,b,h$ and $b,a,h$, respectively, and each uses two
calls. Both types have actual finite origins, for instance current
images $\beta=\rho\alpha$ and $E=\rho\beta$. The union contains the
cycle $a\to b\to a$, although no fixed source follows that cycle.
Replacing $d$ by the actual root address gives the same native example.
The transfers use a single state-local response rule and preserve the
corresponding source paths, so such union cycles and convergences
cause no additional state or call cost. $\square$

### 12.3 Endpoints and the arbitrary-row shared-table consumer

**Corollary 12.6 (complete-output and exact zero-call endpoints).** Put
$m=|G_*[\Theta_*]|=|F[\mathcal U_*]|\ge1$. Every feasible counted
table has at least $m$ halting states and hence $K\ge m$. For $q=0$,
on either side of (NBP.12.8) feasibility is exactly

$$
r\ge m\quad\text{and}\quad K\ge m.
\tag{NBP.12.9}
$$

A constant whole target is feasible with $r=K=1,q=0$, regardless of
the number of reached classes. Empty cuts, a root cut and zero reached
classes have this endpoint. Arbitrary blocked members of a nonempty
cut stay included with their complete predecessor guards. In
particular $r=1,q=0$ is feasible exactly when $m=1$ and $K\ge1$.

**Proof.** Every attained distinct complete target must be the fixed
output of some reached halting state. One halting state has only one
fixed output, giving $|Z|\ge m$. With zero calls, every actual initial
state is already a halt; two different targets cannot share its code.
Thus the actual exported range and the installed state set each have
at least $m$ elements. Conversely install exactly $m$ halts, one with
each attained whole target, and export the code of the correct halt.
The acquired class roots determine this target by Theorem 10.4, so the
producer can actually compute and export the code before the cut.
The root task uses the identical target coloring. No source-dependent
output decoder or free after-entry computation is needed.

The cut and constant cases follow from Corollary 10.10 and this
construction. Its fourth case keeps every already blocked member
absent and every newly blocked occurrence guarded by its predecessor
beta parent. Those are parts of the installed full outputs, not omitted
coordinates. $\square$

**Corollary 12.7 (finite synthesis of shared counted tables on an
arbitrary row).** Given the finite $P,R_*$ with nonempty actual image
fiber and integers $r\ge1,K\ge1,q\ge0$, the bounded abstract
three-budget problem (NBP.12.8) is decidable. A positive answer supplies
a finite acquired encoder and one stationary fixed-address native
Moore table satisfying all three upper budgets on the entire original
fiber under the supplied acquisition, export, isolation and entry
services. No native address-length bound is an input to this criterion.

**Proof.** Proposition 10.2 computes the exact finite attained chart
by (NBP.10.5), and Theorem 10.4 computes each entire $G_*(\theta)$.
Write $Y=G_*[\Theta_*]$. Enumerate state sets
$\{1,\ldots,n\}$ for $1\le n\le K$, all running/halting partitions,
all coordinate maps $Q\to D$, all four-reply transitions into that
same state set, all fixed halt-output maps $Z\to Y$, and all
initial-state colorings $c:\Theta_*\to\{1,\ldots,n\}$ with image
size at most $r$. These choices form a finite set. A nonempty input
chart requires a halt on any successful run. If $D=\varnothing$,
only partitions with no running states admit a coordinate map.

For each candidate and each attained $\theta$, start at $c(\theta)$.
If it is a halt, check its complete output. Otherwise query that
state's coordinate, apply its reply transition and count one call.
Accept this input only if the correct halt is reached after at most
$q$ calls; a running state after the $q$th call fails. This is a finite
check on every input, not a demand that the union graph be a DAG.
All installed states are counted by $n$ whether visited or not. State
sharing, converging edges, repeated coordinates, early halts and union
cycles remain among the enumerated candidates.

Any root table meeting the budgets is isomorphic to one of these
finite labeled state sets. Every halt reached on an attained input
has output in $Y$. Replace the output of each unused halt by any
fixed member of $Y$; this changes neither the state count nor any
actual run. Consequently restricting the enumerated output alphabet
to $Y$ loses no feasible table. Conversely a passing candidate is
exactly a witness to Definition 12.2. Theorem 12.4 proves that these
candidates decide native joint feasibility and installs a passing one
by actual native queries at the representatives $p_d$ and actual
pre-cut export of its initial-state coloring.

The finite enumeration is the consumer of the state-graph transfer,
not its proof. Section 10's decision-tree criterion alone would not
justify this state bound: unrolling a shared graph can duplicate
states. Here Theorem 12.3 first makes the arbitrary finite native
address menu replaceable on the same installed states, and Theorem
12.4 then covers every actual origin. Only after that correspondence
is established does finite shared-table enumeration decide the
arbitrary-row three-budget question. $\square$

### 12.4 Suppliers, attribution and precise realization boundaries

**Mathematical citation 12.8 (the shared-state delta and its scope).**
Definitions 10.1--10.3, Proposition 10.2 and Theorem 10.4 supply the
exact attained chart, actual image admissibility and complete
predecessor factorization. Proposition 10.5 supplies simultaneous
actual finite padding only for a specified finite native address menu;
it retains the full exterior, repeated class values and all
class disequalities. Its prescribed-rank deep-image supplier is
[Retained Literal Root Depth Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md),
and the image grammar and unique inverse are
[Transport--Memory Completion (RA.2207)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md).
The immutable source for §10 is
[revision 3bb8b4fbbc274e21d2de5b0d93a89f6957dc3993](https://github.com/the-omega-institute/trureturing/blob/3bb8b4fbbc274e21d2de5b0d93a89f6957dc3993/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#10-exact-class-root-experiments-on-every-full-actual-one-image-fiber).
Assumption 10.6 supplies actual acquisition/export and entry rather
than deriving them from the finite chart. Definition 11.1 supplies the
counted Moore contract and lawful initial-state-image normalization;
its numerical lower bounds and frontier are not premises here.

Classical state-associated output terminology is attributed to Edward
F. Moore, *Gedanken-Experiments on Sequential Machines*, in *Automata
Studies* (AM-34),
[DOI:10.1515/9781400882618-006](https://doi.org/10.1515/9781400882618-006).
This bibliographic attribution imports no external minimization or
resource-preservation theorem. The bounded source access here supports
that attribution, not a claim to have verified the full paper; none of
the transfer proof depends on an unread external passage. Finite table
enumeration and deterministic state-path induction are ordinary finite
methods. The native query-geometry and protocol-tree precedents remain
attributed to Mathematical citations 9.7 and 10.12 and
[Native Signed Feasibility §§7.1--7.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md).
Those tree results do not preserve total installed Moore states by
themselves.

The repo-derived mathematical delta is the state-local paid response
recoding on one common stationary shared graph, with actual
full-value-dependent initialization restricted only on truthful padded
representatives for necessity, and actual acquired root-color export
for full-fiber sufficiency. Corollary 12.7 is its arbitrary-row
shared-table synthesis consumer beyond the numerical example of §11.
No numerical lower bound is rederived here, no decision-tree reduction
is asserted to have already preserved $K$, and no global novelty or
Lean-kernel claim is made.

The decided problem is existence of an explicitly bounded abstract
table under the supplied acquisition, actual export, complete access
cut, authentication, lawful common entry and stationary native service.
A finite chart certificate does not extract a finite table, its used
states or its longest address from arbitrary program text. A program
with computed addresses or unbounded workspace is not a table of
(NBP.12.1) until its total configurations and transitions have separately
been proved to satisfy that contract. No such extraction is asserted.

The same upper $r,K,q$ equivalence does not preserve an arbitrary fixed
encoder pointwise, every native trace on every original source, native
address widths, installed table or whole-output storage, total physical
memory, acquisition/export work, entry implementation or service time.
For necessity, the exact path comparison is with the selected actual
$u^\theta$ for this table's menu. For sufficiency, the newly installed
native reader is correct on all actual finite origins but need not
imitate the original reader's other traces. A real charged query used
to recode a constant reply adds no free observation or control phase.
Zero classes instead use the constant halt, and zero fresh calls do
not mean zero acquisition. Physical finite-memory realization and
continued research outside this bounded transfer require their own
premises and proofs.

## 追加锚（本行以下为增补区）
## 13. Joint literal-address budgets on the full stationary Moore fiber

### 13.1 Submitted words and shortest reached occurrences

**Definition 13.1 (four upper budgets).** Retain Definitions 10.1--10.3
and 12.1--12.2 without changing their domain or operational premises.
Thus $\mathcal U_*\ne\varnothing$ contains every actual finite ordered
$\alpha/\beta$ origin with $R_P(\rho u)=R_*$, and $\Theta_*$ is its
attained root chart. The complete exterior, reached support $H$,
partition, different-class disequalities and blocked-cut guards remain
fixed. The target is the entire predecessor row
$F(u)=G_*(\theta_x)$ of Theorem 10.4. There is no bound on source size,
depth or intrinsic rank.

For each unchanged class name $d\in D$, choose

$$
a_d=\underset{p\in H,\ [p]=d}{\operatorname{argmin}}\, (|p|,p),
\qquad \lambda(d)=|a_d|.
\tag{NBP.13.1}
$$

The first coordinate is minimized first and the second uses the common
lexicographic order to break ties. This is the shortest physical
occurrence convention of Serial Joint Resource Frontier Lemma 3.4.
The canonical class name is still the original first-hole name; neither
$a_d$ nor $\lambda(d)$ renames it. In particular the first
lexicographic occurrence need not be shortest.

For a terminating native run with successive running-state visits
$b_1,\ldots,b_n$, define its literal submission cost by

$$
\ell_N(u)=\sum_{i=1}^{n}|\operatorname{addr}(b_i)|,
\qquad q_N(u)=n.
\tag{NBP.13.2}
$$

For a root run on $\theta$, replace the summand by
$\lambda(\operatorname{coord}(b_i))$ and write $\ell_R(\theta)$ and
$q_R(\theta)=n$. These are sums along one run before any worst bound.
Each invocation costs one call, including repeated coordinates,
absences and the empty native word, whose literal length is zero.
An initial halt has both costs zero.

For integers $r\ge1,K\ge1,q\ge0,\ell\ge0$, let
$\mathsf{MooreInvFeas}_*(r,K,q,\ell)$ mean Definition 12.1's joint
existence with the additional requirement $\ell_N(u)\le\ell$ for
every $u\in\mathcal U_*$. Let
$\mathsf{MooreRootFeas}_{*,\lambda}(r,K,q,\ell)$ mean Definition 12.2's
joint existence with $\ell_R(\theta)\le\ell$ for every attained
$\theta$. The other requirements remain actual exported initial-state
range at most $r$, all installed running and complete-output halting
states at most $K$, and every run terminating correctly within $q$
calls. Unused states count. The initial-state export is normalized
before the access cut as in (NBP.12.2); only that current state remains
accessible after entry. Both encoder and controller may be reselected.

The added coordinate prices only the physical words actually submitted
to the native port. Address construction, address and table storage,
whole-output representation, local work, elapsed time, acquisition,
export, authentication, isolation, entry and native service retain their
separate costs and supplied premises.

### 13.2 Static forced-successor contraction and the four-budget bridge

**Theorem 13.2 (exact joint four-upper-budget correspondence).** Under
the supplied premises of Definition 12.1, on every nonempty full actual
fixed-row one-image fiber, for all the integers in Definition 13.1,

$$
\mathsf{MooreInvFeas}_*(r,K,q,\ell)
\quad\Longleftrightarrow\quad
\mathsf{MooreRootFeas}_{*,\lambda}(r,K,q,\ell).
\tag{NBP.13.3}
$$

Necessity weakly decreases the four upper resources; sufficiency keeps
the root table's installed states, initialization range, calls and
literal sums on every actual origin. No prescribed-encoder or
unchanged-native-trace assertion is part of the equivalence.

**Proof, static contraction within the native-to-root direction.**
Take a feasible native table on $\mathcal K=Q\sqcup Z$ and its actual
normalized export $\tau$. Let $B\subseteq Q$ consist of all installed
states whose word, when traversed in $C_*$, never enters a reached hole.
For $b\in B$ the complete exterior determines a reply $z_b$ on every
actual current tree in the fiber. Visible ancestors of holes, concrete
leaves, blocked cones and absent extensions of concrete leaves are
included. Put $f(b)=\operatorname{next}(b,z_b)$.

There is at least one installed halt: a nonempty fiber and a terminating
correct run supply one. Fix such a halt $z_0$. Define a single map

$$
g:\mathcal K\longrightarrow\mathcal K\setminus B
\tag{NBP.13.4}
$$

as follows. Outside $B$ it is the identity. Starting inside $B$, follow
$f$ until first leaving $B$ and take that exit as $g(b)$. If the
successor sequence never leaves $B$, take $g(b)=z_0$. Finiteness makes
the latter case exactly eventual entry into a cycle contained in $B$;
the same completion is used for its whole basin.

No actual initialized run can reach that basin. Every reply while in
$B$ is its fixed $z_b$, so such a run would follow the forced cycle
forever, contradicting termination on that same origin. This excludes
only forced constant cycles on required runs, not cycles in the union
of transitions from different sources. It also covers initial states
in $B$: their forced sequence must exit on every actual use.

Install the following reduced native table:

$$
\begin{aligned}
\mathcal K'&=(Q\setminus B)\sqcup Z,\\
\operatorname{addr}'(b)&=\operatorname{addr}(b)
                       &&(b\in Q\setminus B),\\
\operatorname{next}'(b,z)&=g(\operatorname{next}(b,z)),\\
\operatorname{out}'&=\operatorname{out},\qquad
\tau'(u)=g(\tau(u)).
\end{aligned}
\tag{NBP.13.5}
$$

All original halts, their fixed whole outputs and all unused surviving
states remain installed and counted. No state is added. The finite map
$g$ is substituted into the common transition table. Before the cut,
the producer computes and actually exports the new initial-state code
$g(\tau(u))$ from its acquired data, using the supplied lawful entry.
The original export is not retained as an additional field. If the
forced initial sequence exits at a halt, this code initializes that
halt directly. No silent transition, phase, cache or table selection
is executed after entry.

Fix one actual $u$. Delete its $B$-visits from the original finite state
path. Between consecutive remaining states there is either an original
edge or a finite forced $B$-segment. Formula (NBP.13.5) sends the earlier
state directly to the later one. The initial code skips precisely the
initial forced segment. The original terminal halt is retained.
Induction on the remaining visits therefore gives the reduced run and
the same complete output. Its calls and submitted words are exactly
the surviving calls and words of this one original run. Hence

$$
\begin{aligned}
|\tau'[\mathcal U_*]|&\le|\tau[\mathcal U_*]|,&
|\mathcal K'|&\le|\mathcal K|,\\
q_{N'}(u)&\le q_N(u),&
\ell_{N'}(u)&\le\ell_N(u).
\end{aligned}
\tag{NBP.13.6}
$$

The arbitrary completion of a forced-cycle basin is used only on
initial codes or edges that no required actual run takes. It cannot
change these inequalities. This contraction is an intermediate step
of the full-fiber theorem, not a new general epsilon-removal theorem.

**Proof, padded state-local recoding after contraction.** Suppose first
that $D\ne\varnothing$. Every surviving running word enters a reached
hole. Set

$$
L=\max\bigl(\{0\}\cup
 \{|\operatorname{addr}'(b)|:b\in Q\setminus B\}\bigr).
\tag{NBP.13.7}
$$

Unused running states are included. Apply Proposition 10.5, without
reproving its deep actual-image supplier, to obtain one fixed actual
$u^\theta$ for every $\theta\in\Theta_*$. These origins preserve the
entire exterior, repetitions and all class disequalities. Their
branch-valued classes have minimum leaf depth greater than $L$, and
$F(u^\theta)=G_*(\theta)$. This bounds the chosen table's finite address
menu, not the allowed sources.

For each surviving state $b$, write its word as $v=pw$ at the first
entered hole and set $d=[p]$. Reuse the hole-entering part of
(NBP.12.5): $h_v(z)=z$ if $w=\varepsilon$, while for a nonempty suffix
$h_v(\alpha)=h_v(\beta)=\mathsf{absent}$ and
$h_v(\mathsf{branch})=\mathsf{branch}$. Extend $h_v$ arbitrarily to
the unreachable root argument $\mathsf{absent}$. Proposition 10.5
gives $r_{\rho u^\theta}(v)=h_v(\theta(d))$.

On exactly $\mathcal K'$ install coordinate $d$ at this state and
transition $\operatorname{next}'(b,h_v(z))$ on root reply $z$. Retain
the halting outputs and set $c(\theta)=\tau'(u^\theta)$.
This finite coloring has range at most $|\tau'[\mathcal U_*]|$.
It selects truthful actual exports on the chosen witnesses; it does
not require the original arbitrary encoder to factor through root type.

For this one fixed $\theta$, induction on states identifies the entire
root path with the reduced native path on the one actual $u^\theta$,
including early halts, shared states and repeated coordinates.
Every surviving invocation satisfies

$$
\lambda(d)=|a_d|\le |p|\le |pw|=|v|.
\tag{NBP.13.8}
$$

The first inequality is precisely the shortest-occurrence supplier.
Summing only over this common path gives

$$
q_R(\theta)=q_{N'}(u^\theta)\le q_N(u^\theta)\le q,\qquad
\ell_R(\theta)\le\ell_{N'}(u^\theta)\le\ell_N(u^\theta)\le\ell.
\tag{NBP.13.9}
$$

Thus both bounds use the same actual input and truthful initial code
before a worst bound is taken. No separately optimizing origins or
marginal sums are combined. State-local rules handle convergences and
different-source union cycles without cloning histories. Necessity
follows with at most the original $r$ and $K$.

**Proof, root-to-native on every actual origin.** Given a root table
and coloring, retain its entire installed state set, partition,
transitions and complete halting outputs. Replace coordinate $d$ by
the native word $a_d$. The supplier in (NBP.13.1) changes a physical
representative, not its canonical class identity. Every $a_d$ is
reached on every current tree in the original fixed-row fiber and has
reply $\theta_x(d)$ for every actual valuation $x\in\mathcal X_*$.

From its genuinely acquired class values the producer inspects the
roots, computes $\theta_x$ and actually exports $c(\theta_x)$ before
the cut. Local inspection of acquired terms is not a fresh invocation.
Proposition 10.2 makes every type attained, so this actual code range
equals $c[\Theta_*]$. The new code itself is recoverable from the
initial state; no discarded value or separate color register survives.

For an arbitrary original $u_x$, state induction identifies its native
run with the root run on $\theta_x$. Every call is genuine, its word
has exactly length $\lambda(d)$, and repetitions are counted again.
The call counts and literal sums agree on this actual source. The halt
returns $G_*(\theta_x)=F(u_x)$, including inverse exterior, canonical
restricted partition, all disequalities and every predecessor guard.
No padded-witness restriction appears in this direction.

If $D=\varnothing$, Proposition 10.2 gives one empty type and
Theorem 10.4 gives one whole target. On either side, one halt with that
complete output and its one actually exported initial code uses
$r=K=1$ and $q=\ell=0$. There is no running state or nonexistent
coordinate to recode. These resources satisfy every stated upper
budget. This proves (NBP.13.3) in all cases. $\square$

### 13.3 Finite shared-table synthesis and zero-budget endpoints

**Corollary 13.3 (literal sums in the shared-table criterion).** For
finite $P,R_*$ with nonempty actual fiber and the four integer upper
budgets, the joint feasibility problem (NBP.13.3) is decidable. A
positive answer supplies an acquired encoder and one fixed-address
stationary Moore table on the entire actual fiber under the supplied
services.

**Proof.** Reuse Corollary 12.7's finite enumeration of state sets of
size at most $K$, running/halting partitions, coordinates $Q\to D$,
four-reply transitions, whole halt outputs in $G_*[\Theta_*]$, and
initial-state colorings of range at most $r$. Compute $\lambda$ from
the finitely many actual reached occurrences in the complete row.

For each candidate and each attained $\theta$, follow its one run from
$c(\theta)$. At every running visit add one call and
$\lambda(\operatorname{coord}(b))$ to that input's accumulated sum.
Require the correct complete halt within $q$ calls and sum at most
$\ell$. All summands are nonnegative. Reaching a running state after
$q$ calls fails, even if its coordinate has price zero; an initial halt
has zero sum. This is a finite additional check on the existing
enumeration, without a global acyclicity demand.

Every feasible root table occurs in that enumeration up to state
renaming; the existing replacement of unused halt outputs loses no
run or resource. A passing table is a root witness, and Theorem 13.2
installs it using the shortest actual words and acquired initial codes.
Conversely necessity puts every feasible native comparator into the
same bounded finite search. This consumes the four-budget bridge,
rather than trying to infer state preservation from decision-tree
unrolling. No generic weighted minimax theorem is added. $\square$

**Corollary 13.4 (zero calls, zero literal budget and edge cuts).**
Put $m=|G_*[\Theta_*]|=|F[\mathcal U_*]|\ge1$. On either side of
(NBP.13.3), if $q=0$ or if $\ell=0$, feasibility is exactly
$r\ge m$ and $K\ge m$, with the other upper budget arbitrary.
A constant whole target always admits $r=K=1,q=\ell=0$.
Empty cuts, a root cut and zero reached classes have that target;
blocked cuts retain their complete predecessor guards.

**Proof.** The zero-call endpoint is Corollary 12.6: $m$ whole-output
halts and $m$ initial codes are necessary and suffice, and their
literal sum is zero. If $P$ does not contain the root, every reached
occurrence has positive length. Thus every root invocation has
positive price, and a zero literal sum forces zero calls on every
attained input. The same endpoint applies by Theorem 13.2.
If $P$ contains the root, prefix freedom gives $P=\{\varepsilon\}$;
its predecessor target is constant by Corollary 10.10. The one-halt
construction satisfies both zero budgets. Empty and entirely blocked
cuts are the zero-class cases already covered. The guards and
partitions are parts of the whole installed outputs. $\square$

### 13.4 A strict entire-fiber example and the paid-constant boundary

**Proposition 13.5 (one right hole separates length feasibility from
unchanged-path recoding).** Take $P=\{R\}$ and the complete current
row with exterior $\langle\beta,\square_R\rangle$ and its singleton
reached class $d$. Its full actual origin fiber and two entire targets
are

$$
\begin{aligned}
\mathcal U_*&=\{\beta\}\ \cup\
                    \{\langle\alpha,z\rangle:z\in\mathcal T\},\\
F(\beta)&=Y_0=(\beta,\varnothing),\\
F(\langle\alpha,z\rangle)&=
 Y_1=(\langle\alpha,\square_R\rangle,\{\{R\}\}).
\end{aligned}
\tag{NBP.13.10}
$$

Here $Y_0$ has $R$ blocked at its concrete root beta, and $Y_1$ has
$R$ reached; their complete partitions and guards are as displayed.
The chart attains all three types of $d$, and $\lambda(d)=1$.
The four-budget problem is feasible at $(1,3,1,1)$ and infeasible
with $r=1,\ell=0$ for every $K,q$. A native table feasible at
$(1,4,2,1)$ can nevertheless have literal cost two after Theorem
12.3's unchanged-path paid constant-query recoding.

**Proof.** A current tree with this complete row is exactly
$\langle\beta,x\rangle$. For a leaf origin, only $\beta$ works:
its image is $E=\langle\beta,\alpha\rangle$. For a paired origin
$\langle s,z\rangle$, the left image must be beta. The image inverse
(RA.2207) forces $s=\alpha$, and every finite $z$ then works.
This proves the entire fiber in (NBP.13.10), not a finite selection.
Its predecessor rows follow directly from the cut definition.

The right current value is alpha at origin beta and $\rho z$ on every
paired origin. It is respectively beta or branch when $z=\alpha$ or
$z=\beta$, so all three root types are attained. On every paired
origin it is never alpha, by the image grammar. One running state
querying $R$ therefore goes to the complete halt $Y_0$ on alpha and
to $Y_1$ on beta or branch; give its absent edge any existing halt.
A constant actual initial code and these two halts use three states,
one call and literal sum one on the entire fiber.

If $r=1$ and the literal budget is zero, every actually invoked word
must be $\varepsilon$. Its reply is branch on every tree of this
fiber. The common initial state and deterministic stationary rule
then give the identical state path and output on origins beta and
$\langle\alpha,\alpha\rangle$, whose required rows differ.
Termination cannot repair this contradiction, for any $K,q$.
This proves the strict length-budget obstruction directly.

Finally insert an initial running state querying $\varepsilon$ and
going on every reply to the running $R$-state just constructed.
All four installed states are reached on some actual input. Every
run has two calls and literal sum $0+1=1$. In Theorem 12.3 the sole
available root coordinate is $d$: its first paid query is ignored
through the constant response map, and the second queries $d$ again.
Both have price one, so the unchanged path has sum two. The static
contraction in Theorem 13.2 removes the initial exterior-constant
state and exports the surviving state's code; the three-state,
one-call table again has sum one. Thus the stronger unchanged-path
literal domination fails, while the joint upper-budget correspondence
holds. $\square$

### 13.5 Mathematical suppliers and attribution

**Mathematical citation 13.6 (the bounded source-specific composition).**
Proposition 10.2 supplies the attained chart, Theorem 10.4 the whole
predecessor factorization, and Proposition 10.5 the simultaneous actual
image padding. Its suppliers remain
[Retained Literal Root Depth Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md)
and [Transport--Memory Completion (RA.2207)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md).
Definitions 12.1--12.2 supply the stationary state-only shared-table
contract and actual initial-code normalization. The hole-entering
response map of Theorem 12.3 is reused; Proposition 13.5 identifies
the exact literal-cost boundary of its paid constant case.
[Serial Joint Resource Frontier Lemma 3.4](RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md)
already owns shortest physical occurrences and unchanged class names.

[Native Signed Feasibility Proposition 7.4 and Theorem 8.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md)
and [Atomic Block Conjugacy §§6.2--6.4](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md)
already treat same-source literal charges, cleanup or weighted protocol
trees in their respective contracts. They supply no installed-state
bound for this contraction. No cached reply simulation or history
expansion is used to preserve $K$ here.

Classical graph reduction is attributed to Mehryar Mohri,
*Weighted Automata Algorithms*, §6.1, Theorem 4 and its algorithm,
[author PDF pp.21--22](https://cs.nyu.edu/~mohri/pub/hwa.pdf).
The weighted epsilon-removal statement assumes a complete semiring
and computable closures; the displayed returned transducer keeps
the state set $Q$. Randal E. Bryant,
*Graph-Based Algorithms for Boolean Function Manipulation*,
IEEE Transactions on Computers C-35(8), pp.677--691,
[DOI:10.1109/TC.1986.1676819](https://doi.org/10.1109/TC.1986.1676819),
Definition 5 and §4.2,
[author PDF pp.5,10--11](https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf),
gives the redundant-vertex reduction for ordered acyclic Boolean
function graphs. These inspected passages are structural precedents,
not premises about paid native invocations, lawful acquired export,
forced-cycle basins or four-budget full-fiber feasibility. Theorem
13.2 proves those obligations directly.

The result is repo-derived synthesis of these mature graph methods
with the actual one-image and shortest-occurrence suppliers. Its
consumer is Corollary 13.3's per-attained-input literal check on the
existing shared-table enumeration. It makes no global novelty or
Lean-kernel claim. Joint encoder/controller reselection and upper
budgets are essential to the stated transfer; exact original graphs,
call counts and traces, prescribed-encoder performance, arbitrary
program extraction and physical resource certification remain outside
it. No additional update or observation service is supplied.

## 追加锚（本行以下为增补区）


## 14. Paid common-start preparation and code-only two-phase feasibility

### 14.1 The full fiber and the changed pre-cut permission

**Assumption 14.1 (same-register paid preparation and actual handoff).**
Fix precisely the nonempty full actual fiber $\mathcal U_*$,
class valuations $\mathcal X_*$, attained root chart $\Theta_*$ and
whole predecessor target $F(u)=G_*(\theta_x)$ of Definitions
10.1--10.3 and Theorem 10.4. Write $H_*$ for the fixed reached-hole
support denoted $H$ there; $H$ below is a preparation-state budget.
Retain the finite ordered source grammar,
the single authenticated actual update $t=\rho u$, every repetition,
different-class disequality and absent-cut guard, and every finite
origin in that fiber. Keep the complete $P,R_*$ lawfully acquired.
There is no restriction on source size, depth, rank or hidden values.

Replace only the full-value-possession premise of Assumption 10.6:
a new preparation begins from one fixed source-independent state,
depending on $P,R_*$ and common installed tables. Neither the current
tree nor any class subtree value is an input to that state. Any archive
used to acquire the complete row is inaccessible to this preparation.
Preparation is now explicitly permitted to invoke the same authenticated
four-reply native register before the access cut. Every finite word is
legal. The register is stationary throughout preparation, handoff and
reading; there is no intervening update, change of root or source
replacement. This pre-cut permission is an added operational premise,
not a consequence of the old acquired-value contract.

Preparation obtains its source distinctions only from these actual
paid replies. It reaches a complete code latch, actually exports its
code and stops. A supplied paid handoff makes all preparation state and
material inaccessible, and lawfully enters the reader with that code
as its entire mutable accessible state. The old stop is absorbing;
reader entry is a new supplied invocation, not an action by a stopped
producer. Authentication and public entry controls select no origin
within $\mathcal U_*$. The reader has the common row, cut and installed
tables, but no other source-bearing field: no values, archive, handle,
pointer, transcript, acquisition order, counter, timing, code length,
meter or source-dependent table selection. Inaccessible material need
not be physically erased.

The actual handoff transfers exactly one complete reader-state code.
No source call or source-dependent computation intervenes between the
latch and entry. Export, isolation and lawful entry are paid services,
with their own declared prices, even for a constant code and an immediate
reader halt. No generation, equality, image, provenance or inverse
port is supplied. The ordinary inverse parser and complete output rows
remain common finite mathematical data, not physical inverse actions.

**Definition 14.2 (terminal-latch convention and seven upper budgets).**
Choose one finite reader alphabet
$\mathcal K=Q\sqcup Z$ and exactly the shared stationary tables
$\operatorname{addr}_R,\operatorname{next}_R,\operatorname{out}$
of (NBP.12.1). Each running state has one fixed finite native word,
each transition depends only on its actual reply, and each halt has
one fixed whole predecessor-row output. There is no after-entry
output decoder or auxiliary register.

Choose a nonempty installed set of codes $S\subseteq\mathcal K$ and
a disjoint preparation alphabet

$$
\mathcal B=V\sqcup\widehat S,\qquad
\widehat S=\{\widehat s:s\in S\},
\qquad b_0\in\mathcal B,
\tag{NBP.14.1}
$$

with one common initial state $b_0$ and fixed tables

$$
\operatorname{addr}_P:V\longrightarrow\{L,R\}^*,
\qquad
\operatorname{next}_P:V\times\mathcal A\longrightarrow\mathcal B,
\qquad
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}.
\tag{NBP.14.2}
$$

At $v\in V$, one actual native invocation at
$\operatorname{addr}_P(v)$ supplies the reply for
$\operatorname{next}_P$. A terminal state $\widehat s$ is an atomic
latch holding the complete code $s$. It makes no native call.
The last preparation transition replaces the running state by this
latch; if $b_0$ is a latch its code is a common constant. The latch
has no additional continuing preparation control. A fixed paid
handoff transfers that actual code and enters precisely state $s$,
with the preparation alphabet thereafter inaccessible.

This convention counts the live preparation control and the code
latch in one alphabet, rather than supplying a separate free code
register. During preparation the whole mutable configuration is one
member of $\mathcal B$; in a terminal configuration it includes the
latched code. During reading it is one member of $\mathcal K$.
The phase and terminal status are part of these disjoint tagged
configurations, not an uncharged mutable phase bit. There is no
simultaneously live preparation/latch pair hidden behind a state
name: the terminal latch replaces preparation control. A realization
that retains both independently must charge those joint configurations
and is outside this convention unless separately related to it.
The handoff's physical transient storage and control have their own
service prices; their realization is not inferred from the abstract
replacement operation.

All installed members of $\mathcal B$ and $\mathcal K$ count,
including unused running states, unused latches, unused halts and
different halts with the same output. Preparation latches carry literal
reader-state codes, so their transfer uses inclusion into $\mathcal K$,
not a code-dependent decoder. Fixed addresses, all four transition
entries, latch labels and whole-output entries are installed common
table data. The two cardinality budgets below charge every installed
state record; the representations of these tables, words and complete
rows, installation work and local transition work have separate prices.
These cardinalities are not a claim about total physical bits.

For each actual $u$, the preparation must terminate at some
$\widehat{\tau(u)}$. Its genuinely generated and actually exported
code is $\tau(u)\in S$. Starting the reader at that code must terminate
with $F(u)$. If $v_1,\ldots,v_a$ and $w_1,\ldots,w_b$ are the respective
running-state visits of this same execution, put

$$
\begin{aligned}
q_P(u)&=a,&
\ell_P(u)&=\sum_{i=1}^{a}|\operatorname{addr}_P(v_i)|,\\
q_R(u)&=b,&
\ell_R(u)&=\sum_{j=1}^{b}|\operatorname{addr}_R(w_j)|.
\end{aligned}
\tag{NBP.14.3}
$$

Every invocation is charged, including a repeated word, absence,
a word previously invoked in the other phase and the empty word.
The empty word costs one call and zero literal letters.
No caching discounts a later invocation. An immediate latch or halt
has zero native calls and zero literal sum in its phase. The one
actual handoff still occurs and is charged separately.

For integers $r,H,K\ge1$ and $p,\ell_P,q,\ell_R\ge0$, write

$$
\mathbf b=(r,H,K,p,\ell_P,q,\ell_R).
\tag{NBP.14.4}
$$

Let $\mathsf{PaidNative}_*(\mathbf b)$ mean joint existence of the
two installed tables, common start and actual handoff just specified,
under Assumption 14.1, such that

$$
\begin{gathered}
|\tau[\mathcal U_*]|\le r,\qquad
|\mathcal B|\le H,\qquad|\mathcal K|\le K,\\
q_P(u)\le p,\quad\ell_P(u)\le\ell_P,\quad
q_R(u)\le q,\quad\ell_R(u)\le\ell_R
\qquad(u\in\mathcal U_*).
\end{gathered}
\tag{NBP.14.5}
$$

The scalar $\ell_P$ or $\ell_R$ on the right is the corresponding
upper budget; the argumented symbol on the left is the per-source
sum. The actual export range can be smaller than the installed
latch set. Neither is a supplied coloring of unknown sources.
The budgets concern a coupled execution: the reader's initial state
is what this preparation actually generates on this same source.
The installed tables and all seven upper bounds are chosen jointly.

The terminal-latch convention is sufficient to express code-only
stopping preparation without an independent surviving producer state.
It does not assert that every physical preparer can attain that
convention or that the two cardinalities combine by addition or
maximum into physical memory. Table storage, fixed output storage,
authentication, row acquisition, pre-cut permission, native service,
export, isolation and entry retain their separately paid premises.

### 14.2 The finite root task has a generated code

**Definition 14.3 (coupled root-table feasibility).** Reuse exactly
$\Theta_*$, $G_*$ and the shortest reached occurrences $a_d$ and
prices $\lambda(d)=|a_d|$ of (NBP.13.1); canonical class names are
unchanged. A root preparation and root reader have precisely the
alphabets, latches, common start, transitions and whole outputs of
Definition 14.2, except that the two running-state address maps become

$$
\operatorname{coord}_P:V\longrightarrow D,\qquad
\operatorname{coord}_R:Q\longrightarrow D.
\tag{NBP.14.6}
$$

An invocation at either running state returns the corresponding
$\theta(d)$ on input $\theta\in\Theta_*$. It costs one call and
$\lambda(d)$ literal letters. Repeat invocations are charged anew.
The fourth transition entry is installed and counted, but absence
is unattained at these reached class roots. There is no constant-query
port, silent local control phase or arbitrary initial coloring.

The preparation starts at the same $b_0$ for every attained input.
Its terminal latch defines the induced code $c(\theta)\in S$.
Only after that run and its paid code transfer does the root reader
start at $c(\theta)$. Let
$\mathsf{PaidRoot}_{*,\lambda}(\mathbf b)$ require correctness
$G_*(\theta)$, range $|c[\Theta_*]|\le r$, installed cardinalities
$H,K$, and the separate call and literal upper bounds in
(NBP.14.5), now computed along these two runs on this one $\theta$.
The root task is a finite comparison presentation; it adds no new
port to the actual source.

If $D=\varnothing$, both coordinate maps force $V=Q=\varnothing$.
The singleton attained empty type and its whole target admit one
common code latch and one complete-output halt, with zero native
costs in both phases and one actual paid handoff. This is within
every budget vector in (NBP.14.4).

### 14.3 The same-budget correspondence on both shared graphs

**Theorem 14.4 (paid common-start full-fiber correspondence).**
Under Assumption 14.1 and the terminal-latch convention, on every
nonempty full actual fixed-row one-image fiber, for every vector
$\mathbf b$ of (NBP.14.4),

$$
\mathsf{PaidNative}_*(\mathbf b)
\quad\Longleftrightarrow\quad
\mathsf{PaidRoot}_{*,\lambda}(\mathbf b).
\tag{NBP.14.7}
$$

Necessity weakly decreases each of the seven upper resources.
Sufficiency preserves the root witness's installed alphabets,
actual code range, phase call counts and phase literal sums.
Both directions retain one actual paid code-only handoff.
The comparison is joint table existence, not preservation of an
arbitrary prescribed encoder, graph or native trace.

**Proof, coupled contraction of exterior-constant states.**
Take a feasible native pair. Let $B_R\subseteq Q$ and $B_P\subseteq V$
be the installed states whose words, traversed in the fixed exterior
$C_*$, never enter a reached hole. Their replies are fixed on the
entire fiber, including visible ancestors, exterior leaves, blocked
cones and absent extensions. Use the finite forced-successor map
of Theorem 13.2 on the reader:

$$
g_R:\mathcal K\longrightarrow
\mathcal K'=(Q\setminus B_R)\sqcup Z.
\tag{NBP.14.8}
$$

It is the identity outside $B_R$, follows constant successors to
their first exit, and sends a forced-cycle basin to a fixed existing
halt. Such a halt exists by nonempty-fiber termination. A forced
cycle cannot be reached from any actually generated code on its
source: its fixed replies would prevent that required reader from
terminating. Theorem 13.2's static substitution therefore applies
to every actual reader path, regardless of how its initial code
was prepared. It removes only constant-state visits from that path.

The acquired-value encoder replacement used in §13 is not available
for free here. Instead set

$$
S'=g_R[S],\qquad
\mathcal B'=(V\setminus B_P)\sqcup\widehat{S'}.
\tag{NBP.14.9}
$$

Every old terminal latch $\widehat s$ is replaced by
$\widehat{g_R(s)}$; equal new codes share one latch.
This is a common replacement of installed terminal labels.
It makes the new preparation generate $g_R(\tau(u))$ by its own
transitions, rather than asking an external encoder to supply it.

Define a fixed map $g_P:\mathcal B\to\mathcal B'$.
At a surviving running state it is the identity.
At an old latch it is the replacement just specified.
Starting in $B_P$, follow the original constant-reply successors
until the first state outside $B_P$, and apply these rules there.
For a constant cycle and its basin, choose any fixed latch in
$\widehat{S'}$. This alphabet is nonempty. No required preparation
can reach such a basin: its initial state is common, its replies
within the basin are fixed, and on any source that reached it the
preparation would fail to terminate. Finiteness decides each
successor chain of this particular installed graph.

Install the reduced preparation with the common start
$g_P(b_0)$ and transition table

$$
\operatorname{next}'_P(v,z)
 =g_P(\operatorname{next}_P(v,z))
 \qquad(v\in V\setminus B_P).
\tag{NBP.14.10}
$$

Keep each surviving preparation word. Install the reduced reader
with its surviving words, original whole halting outputs and
$\operatorname{next}'_R(w,z)=
g_R(\operatorname{next}_R(w,z))$.
All these substitutions are in common fixed tables.
The latch code already is $g_R(s)$; no live decoder or silent
post-entry step executes either map.
The new common start is a fixed state, not a source-dependent value.

For one fixed actual $u$, delete $B_P$-visits from its finite
preparation path and rename its terminal latch. Equation
(NBP.14.10) connects exactly the surviving visits, ending at
$\widehat{g_R(\tau(u))}$. The actual handoff exports that generated
code. The reduced reader then has precisely the original reader
path on this same $u$ with its $B_R$-visits deleted, beginning after
any forced initial segment. It ends at the same complete halt.
This is the static path argument of Theorem 13.2 applied with the
coupled latch replacement, not independent choice of two encoders.

Consequently, with $\tau'(u)=g_R(\tau(u))$,

$$
\begin{gathered}
|\mathcal B'|\le|\mathcal B|,\qquad
|\mathcal K'|\le|\mathcal K|,\qquad
|\tau'[\mathcal U_*]|\le|\tau[\mathcal U_*]|,\\
q'_P(u)\le q_P(u),\quad \ell'_P(u)\le\ell_P(u),\qquad
q'_R(u)\le q_R(u),\quad \ell'_R(u)\le\ell_R(u).
\end{gathered}
\tag{NBP.14.11}
$$

Each cost inequality is deletion of nonnegative summands on the
same actual source's phase path. Every unused surviving state and
latch still counts. Arbitrary completions of forced-cycle basins
are unreachable on required runs. The construction removes
constant queries by changing the common start, transitions and
latches; it does not perform free runtime transitions.

**Proof, one padding family for the two remaining menus.**
Assume $D\ne\varnothing$. Every surviving running word enters a
reached hole. Let $L$ be the maximum of zero and the lengths of
all installed surviving words in both phases, including unused
states. Proposition 10.5 at this single $L$ supplies actual finite
origins $u^\theta$ for every $\theta\in\Theta_*$.
Their current trees retain the complete row, all repetitions,
disequalities and absence guards. Branch class values have minimum
leaf depth greater than $L$, and
$F(u^\theta)=G_*(\theta)$.
This bounds the chosen menus, not the source domain.

At either phase's state, write its fixed word as $v=pw$ where
$p\in H_*$ is the first entered hole, and put $d=[p]$.
Reuse (NBP.12.5) and Proposition 10.5:

$$
r_{\rho u^\theta}(v)=h_v(\theta(d)),\qquad
h_v(z)=
\begin{cases}
z,&w=\varepsilon,\\
\mathsf{absent},&w\ne\varepsilon,\
                  z\in\{\alpha,\beta\},\\
\mathsf{branch},&w\ne\varepsilon,\
                  z=\mathsf{branch}.
\end{cases}
\tag{NBP.14.12}
$$

Extend $h_v$ arbitrarily at the unattained root argument
$\mathsf{absent}$. At that state install coordinate $d$ and
replace its transition on $z$ by its reduced native transition
on $h_v(z)$. Do this on both installed graphs, keeping
$\mathcal B',\mathcal K'$, their latches, the common start and
all whole outputs.

Fix one $\theta$. State induction makes the root preparation
identical to the reduced native preparation on this one actual
$u^\theta$, hence it really reaches the latch with code

$$
c(\theta)=\tau'(u^\theta).
\tag{NBP.14.13}
$$

This equality describes the generated code; it is not permission
to install $c$ as a free source-dependent start.
Both paired readers then start at this same code, and a second
state induction identifies their paths and complete outputs.
Using a different padding representative for the reader would
not justify this step. Here both menus were padded together and
both paths concern the same stationary realization.

For every corresponding call in either phase, the shortest
physical occurrence supplier gives

$$
\lambda(d)=|a_d|\le |p|\le|pw|=|v|.
\tag{NBP.14.14}
$$

Calls agree along each compared path. Summing this inequality
separately over its preparation and reader visits, and then using
(NBP.14.11), proves the respective upper bounds $p,\ell_P,q,\ell_R$.
The generated root code range is at most the reduced actual range
because (NBP.14.13) uses actual sources. Installed state bounds
are those of (NBP.14.11).
No history unrolling or state cloning is used. Shared states,
converging paths and cycles in the union of different-source paths
obey one state-local transition map.
This proves native-to-root necessity.

**Proof, actual paid preparation on every original origin.**
Given a feasible root pair, replace every coordinate $d$, in both
phases, by the native shortest reached occurrence $a_d$.
Keep the entire installed alphabets, common start, transition
tables, terminal latch codes and whole halting outputs.
For every original $u_x\in\mathcal U_*$, every such occurrence
is reached and its actual native reply is $\theta_x(d)$.
Proposition 10.2 puts this attained type in $\Theta_*$.

Induction on the preparation states therefore gives its root
path on $\theta_x$, one genuine paid invocation at each running
visit, and exactly the root path's call count and literal sum.
It ends at the actual latch $\widehat{c(\theta_x)}$.
No class value or complete source was supplied to compute that
code, and no computation inspects an unacquired value.
Assumption 14.1 then supplies the one actual charged export,
isolation and lawful entry into state $c(\theta_x)$.
The reader has only this state and common data.

Reader-state induction gives the root reader path on $\theta_x$
with the same separate costs and whole output
$G_*(\theta_x)=F(u_x)$ by Theorem 10.4.
The output includes inverse exterior, canonically restricted
partition, all class disequalities and all predecessor blocking
guards. This holds for every original finite origin, without
a padding restriction. Every root type is attained, so the
actual code range is exactly $c[\Theta_*]$.
The installed cardinalities are unchanged and each coordinate
call has literal cost exactly $\lambda(d)$.

If $D=\varnothing$, the common constant target and the one-latch,
one-halt construction of Definition 14.3 give both feasibility
statements for all allowed vectors. It also performs the actual
paid handoff. No nonexistent coordinate is queried.
This completes all cases of (NBP.14.7). $\square$

### 14.4 The existing finite synthesis consumer with a preparation graph

**Corollary 14.5 (finite criterion for the coupled budgets).**
For finite $P,R_*$ with nonempty actual fiber and any vector
$\mathbf b$ of (NBP.14.4), the bounded joint feasibility in
(NBP.14.7) is decidable. A positive finite certificate specifies
the common-start native preparation and state-only reader on
the entire original fiber, conditional on Assumption 14.1.
The code is generated by preparation, rather than selected
from an independently supplied coloring.

**Proof.** Compute the attained chart and each whole target using
Proposition 10.2 and Theorem 10.4, and compute $\lambda$ by
(NBP.13.1). Reuse Corollaries 12.7 and 13.3's finite inventory
of reader state sets of size at most $K$, running/halting
partitions, class-coordinate labels, four-reply transitions
and whole halt outputs in $Y=G_*[\Theta_*]$.
There is no need to enumerate arbitrary native words.

For each reader candidate, choose a nonempty installed
$S\subseteq\mathcal K$. Add a preparation running set $V$
with $|V|+|S|\le H$, latches $\widehat S$, a single start
in $V\sqcup\widehat S$, coordinate labels $V\to D$ and
four-reply transitions into that same preparation alphabet.
All choices are finite up to state renaming.
This replaces the arbitrary initial-coloring choice of the
earlier consumer by a counted common-start preparation graph;
it does not assume that every coloring can be prepared.

For each $\theta\in\Theta_*$, follow the preparation from its
common start. At each running visit add one call and its
coordinate price. Require a latch within $p$ calls and sum
at most $\ell_P$. From that reached latch's literal reader
code, follow the candidate reader, requiring the correct
whole halt within $q$ calls and sum at most $\ell_R$.
A still-running state at its phase's call limit fails even
when its coordinate price is zero. Record the generated codes
over all attained inputs and require their range at most $r$.
Installed unused states and latches count against $H,K$;
union-graph cycles are not excluded unless a required run
actually fails.

The bounded phase simulations terminate this finite test.
Every feasible root pair occurs in this inventory after
renaming. As in Corollary 12.7, the output of an unused
reader halt may be replaced by any fixed member of nonempty
$Y$, without changing any required path or resource.
Conversely a passing pair is precisely Definition 14.3.
Theorem 14.4 then proves completeness for all native pairs
and installs a passing pair by actual queries at $a_d$ in
both phases. Necessity is what makes this finite root
inventory exhaustive despite arbitrary native finite words.

This is an additional coupled use of the existing shared-table
consumer. It is not an implementation enumerator, a generic
automata minimization theorem, or an extraction procedure for
arbitrary program text with computed addresses or unbounded
workspace. $\square$

### 14.5 Preparation cannot manufacture a free initial coloring

**Proposition 14.6 (zero-information preparation obstruction).**
Let $m=|F[\mathcal U_*]|=|G_*[\Theta_*]|\ge1$.
In Definition 14.2, zero preparation calls force one actual
export value, independently of the permitted $r,H,K$.
If both phase call budgets are zero, feasibility is exactly
$m=1$, for every $r,H,K\ge1$ and arbitrary nonnegative
literal upper budgets. If the root is not cut, zero
preparation literal budget also forces a constant actual code,
even with an arbitrary finite preparation-call upper budget.

More generally, if two actual sources give identical replies
along the common preparation path, they reach the same code.
If their reader replies from that code also agree along the
reader path, a correct pair must give them the same whole target.
The corresponding statement holds on the root task.

**Proof.** At zero preparation calls the common initial state
must already be a terminal latch on the nonempty domain;
otherwise a required run invokes its running-state word.
Its code is fixed. At zero reader calls the common exported
code must already be a reader halt and gives one fixed output.
Thus correctness on the entire fiber requires $m=1$.
Conversely its one whole target, one common code latch and
one fixed-output halt suffice, with zero native costs and
one actual paid handoff.

With the root uncut, the complete fixed exterior determines
the current root constructor on every source of the fiber.
A zero literal sum allows only empty-word invocations.
Their replies are therefore constant. Induction from the
common start makes all preparation state paths identical
and their terminal code constant. Repeating a zero-length
word costs another call but adds no distinction.

For the general statement, determinism gives equal next
states from equal current states and equal replies, first
through preparation and then from the identical code
through reading. A terminating identical reader path has
one fixed whole output, so the targets must agree.
This also proves the finite-root version.
If the root is cut, prefix freedom gives
$P=\{\varepsilon\}$ and the whole target is constant by
Corollary 10.10; a zero-length call can then distinguish
current root types but is still charged.
These claims neither deny positive-information paid
preparation nor transfer AG's different-port impossibility.
$\square$

**Proposition 14.7 (strict paid-preparation example on the entire
one-right-hole fiber).** Use exactly Proposition 13.5's cut
$P=\{R\}$, current exterior
$\langle\beta,\square_R\rangle$, singleton class $d$ and
whole targets $Y_0,Y_1$. In the coordinate order of
(NBP.14.4), both vectors

$$
(2,3,2,1,1,0,0)
\qquad\text{and}\qquad
(1,1,3,0,0,1,1)
\tag{NBP.14.15}
$$

are feasible on its entire original fiber.
Any vector with $p=q=0$ is infeasible there, regardless of
$r,H,K$. Even if both call upper bounds are positive,
$\ell_P=\ell_R=0$ is infeasible for arbitrary $r,H,K$.

**Proof.** Reuse, without selecting a finite subfiber,
the supplier's exact description

$$
\mathcal U_*=\{\beta\}\cup
 \{\langle\alpha,z\rangle:z\in\mathcal T\},
\qquad
F(\beta)=Y_0,\quad
F(\langle\alpha,z\rangle)=Y_1.
\tag{NBP.14.16}
$$

The current reply at $R$ is alpha precisely on origin
$\beta$; every paired origin gives beta or branch.
These are Proposition 13.5's full-fiber conclusions,
and $\lambda(d)=1$.

For the first vector, install two reader halts $z_0,z_1$
with whole outputs $Y_0,Y_1$. Install preparation states
$v,\widehat{z_0},\widehat{z_1}$ and common start $v$.
At $v$ actually query $R$, go to $\widehat{z_0}$ on
alpha and to $\widehat{z_1}$ on beta or branch; assign
the unattained absence edge either existing latch.
Preparation has one call and literal sum one.
Its two codes are both actually attained.
The actual handoff enters the corresponding reader halt,
which needs no call. All three preparation/latch states
and both reader halts are installed and counted.

For the second vector, use the supplier's three-state
reader: a state $w$ querying $R$ and the two whole halts,
with the same reply-to-target rule. The preparation is
the single common latch $\widehat w$. Its code is constant
and its native costs are zero. After the actual paid
handoff the reader pays one call and one literal letter.
This constructs each asserted vector on every source
in (NBP.14.16).

The whole target has two values, so Proposition 14.6
excludes $p=q=0$ even if the export upper capacity is
large. For the last claim, all invoked words in either
phase must be empty. The current root reply is branch
on the entire fiber. Common-start preparation therefore
generates one code, and the reader from it follows one
identical deterministic path on every origin. Its one
output cannot equal both $Y_0$ and $Y_1$.
No additional numerical frontier is needed.

In contrast, Corollary 12.6 permits the acquired-value
producer to export the correct one of two whole-output
halt codes with zero reader calls. It does not assign
zero cost to acquiring those values and does not provide
a zero-query common-start preparation. Here the first
vector explicitly pays the necessary discriminating
preparation query. $\square$

### 14.6 Attribution and remaining operational boundaries

**Mathematical citation 14.8 (source-specific suppliers and literature
scope).** The source, four native replies and legality of every
finite word are Definition 1.1 and
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
readout. The complete legal-row representation and its
disequalities are supplied by
[NativeCutFibers](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean),
legal_values_row and rowFiberEquiv.
Theorem 14.4 uses Proposition 10.2's attained chart,
Theorem 10.4's whole predecessor target,
Proposition 10.5's simultaneous actual image padding,
Theorem 12.3's state-local hole-response function and
Theorem 13.2's static constant-state contraction.
Their source identity is the owning volume at revision
[42868fd90886d99005c46c367ca502df5090c447](https://github.com/the-omega-institute/trureturing/blob/42868fd90886d99005c46c367ca502df5090c447/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md).

The deeper padding supplier is
[Retained Literal Root Depth Theorem 2.2](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md):
finite free terms, a finite list of syntactically unequal
negative pairs after fixed ground expansion, independently
prescribed ranks, and one common minimum-leaf-depth lower
bound. In the application of Proposition 10.5, its
branch slots have rank one and hence are actual images;
the constructed values retain repetitions and all required
disequalities together. The image grammar and unique
inverse are
[Transport--Memory Completion (RA.2207)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md).
Shortest occurrence pricing is
[Serial Joint Resource Frontier Lemma 3.4](RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md)
and (NBP.13.1), without renaming any class.
Corollaries 12.7 and 13.3 supply the finite reader-table
inventory consumed by Corollary 14.5.

Paid preparation itself is already present in
[Retained Literal Root Depth Definition 4.3](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md)
and its Theorem 4.4. That preparation pays for a full
native traversal and computes a code, using the
sourcewise finite acquisition of its Theorem 4.2.
It has no uniform all-source traversal-cost bound.
The sourcewise native acquisition theorem
acquisition_foundation likewise supplies its own
source-dependent trace, not a fixed finite preparation
alphabet or the bounds in (NBP.14.5).
The mathematical addition here is the bounded same-port
two-phase correspondence with an induced initial code,
a counted terminal latch and its coupled finite consumer.

Classical state-associated output terminology is attributed
to Edward F. Moore,
*Gedanken-Experiments on Sequential Machines*, in
*Automata Studies* (AM-34),
[DOI:10.1515/9781400882618-006](https://doi.org/10.1515/9781400882618-006).
This is bibliographic attribution only; no proposition
from that paper is used. The Mohri weighted epsilon-removal
and Bryant ordered acyclic graph precedents cited in
Mathematical citation 13.6 are also not premises of this
two-phase theorem. In particular no unread primary
literature claim supplies preparation, export, state bounds
or same-source coupling. The proofs here use the stated
repository suppliers and ordinary finite path arguments.
The composition is repo-derived and carries no claim of
global novelty.

**Assumption 14.9 (limits of operational interpretation).**
The hypotheses of Assumption 14.1 must be provided for any
physical application: lawful complete-row acquisition,
fresh common-start pre-cut access to the same stationary
register, installation of the selected tables, actual code
export, complete isolation and lawful new entry.
Theorem 14.4 is not a construction of those services.
It preserves the declared abstract state-record and
per-run native budgets, not table byte sizes, total
physical memory, elapsed time, energy, fabrication,
address generation or transient handoff workspace.
Its fixed one-handoff convention does not quantify a
physical write/erase instruction implementation.

The additional faithful aligned generation-bit port,
origin synchronization and protected latch of
[Atomic Generation Acquisition §§9--11](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md)
belong to that KBonacci source and action contract.
They provide no port or preparation construction for
this finite ordered-tree fiber. Its original-endpoint
impossibility has different operations and cannot be
transferred merely by identifying both tasks as recovery.

The
[paid core-return and menu re-entry result at its published source](https://github.com/the-omega-institute/trureturing/blob/4b808e6080d/Blueprint/D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/ReturnMenu.md)
retains the producer core and explicitly leaves full
canonical Ready, live fresh service and COMPLETE/U
unresolved. It does not discharge the code-only isolation
or new-entry premise here.
[Native Presburger decisions](https://github.com/the-omega-institute/trureturing/blob/4b808e6080d/Blueprint/D5/S0/Computability/NatPresburgerSolver.md)
and
[NoEvenCycleRank](https://github.com/the-omega-institute/trureturing/blob/4b808e6080d/Blueprint/D5/S3/Combinatorics/Graph/Walks/NoEvenCycleRank.md)
supply no correspondence of native operations,
preparation configurations or resource prices for
(NBP.14.7); neither is used as a premise.

An arbitrary fixed-coloring reader from §§10--13 becomes
a witness here only if a preparation graph with the
declared budgets actually generates its initial codes.
An arbitrary program becomes a table witness only after
its full configurations, fixed state-address rule,
transitions and source inputs meet Definition 14.2.
No program extraction, global numerical optimum or
physical implementation follows from finite synthesis.
The new propositions are ordinary mathematical
statements and proofs; no Lean-kernel evidence is
asserted for this two-phase layer.

## 追加锚（本行以下为增补区）

## 15. Prescribed binary history codes at the two-call eight-state boundary

### 15.1 The fixed code and the entire actual domain

**Definition 15.1 (prescribed-code compatibility).** Retain exactly
$\mathcal U_*$, $P$, $R_*$, the actual class values $x_d$, and the five
complete predecessor rows $R_0,\ldots,R_4$ of Definition 9.1 and
Proposition 9.3. Write

$$
D=\{a,c,b_1,b_2,b_3,b_4\},\qquad
J=\{1,2,3,4\},\qquad J_a=\{1,2\},\quad J_c=\{3,4\}.
\tag{NBP.15.1}
$$

All finite ordered native origins in this fiber remain allowed. Keep
Assumption 9.2's genuine acquisition on the authenticated current version,
actual export, complete access cut, lawful common entry and stationary
native service. In particular the available acquired data $A(u)$ are the
lossless current tree or the complete current row with its six acquired
finite class values. Fix a specified lawful finite computation $\kappa$
on those data, and prescribe the complete exported code

$$
\sigma(u)=\kappa(A(u))\in\{0,1\}\qquad(u\in\mathcal U_*).
\tag{NBP.15.2}
$$

The code may depend on the internal structure of the acquired terms.
It need not factor through their roots or through the predecessor row.
Its acquisition and computation are supplied pre-cut operations, with
separate prices. No assertion below supplies acquisition, authentication,
export, access isolation, entry or service continuity from a representation.

Use precisely the stationary Moore controller of Definition 11.1:
one finite installed set $\mathcal K=Q\sqcup H$, one fixed literal
address per running state, all four reply successors, and one fixed
whole row per halt. The only accessible source-dependent state after
entry is the current member of $\mathcal K$. Initialization is the
same function $\iota(\sigma(u))$ on every source. The initial state
must recover the prescribed complete code on its attained range.
The code and acquired archive cannot be accessed again after entry;
there is no additional source argument, address computation, selector,
phase, counter or output decoder. Every installed state counts, and
every running visit makes and pays for exactly one actual native call.

Call $\sigma$ compatible if one such common controller returns the
entire $F(u)=R_P(u)$ on every $u\in\mathcal U_*$ in at most two calls,
with at most eight total installed states. The code in (NBP.15.2) is
held fixed in this existence question. No pre-cut replacement of it by
a more convenient initial-state code is allowed. The lower arguments
also allow a merging $\iota$; success will force its two used values
to have different entries, hence the required entry recoverability.

**Proposition 15.2 (whole root fibers and movable six-source families).**
Put $\mathcal B=\{x\in\mathcal I:r_x(\varepsilon)=\mathsf{branch}\}$,
where $\mathcal I=\rho[\mathcal T]$. The following are nonempty,
pairwise disjoint subsets whose union is the entire $\mathcal U_*$:

- $\Pi_j$, for $j\in J$: $x_{b_j}=\alpha$, its partner is $\beta$,
  and all other class roots are branches;
- $Z_d$, for $d\in D$: $x_d=\beta$ and all other class roots are branches;
- $Z_*$: all six class roots are branches.

Here each set contains every actual origin with its specified root
profile, with no restriction on the finite branch values beyond the
original image and class-disequality conditions. The target is $R_j$
on $\Pi_j$ and $R_0$ on every $Z_d$ and on $Z_*$. On every source,
a query at a representative occurrence $p_d$ reads the actual root of
$x_d$, and any address $p w$ entering a hole satisfies (NBP.9.7).

Moreover choose any six pairwise different values $B_d\in\mathcal B$.
There are six simultaneous actual sources indexed by
$Z=\{0_a,0_c,1,2,3,4\}$ with class values

$$
\begin{aligned}
x_a^{(z)}&=\begin{cases}\beta,&z\in\{0_a,1,2\},\\
                         B_a,&z\in\{0_c,3,4\},\end{cases}\\
x_c^{(z)}&=\begin{cases}B_c,&z\in\{0_a,1,2\},\\
                         \beta,&z\in\{0_c,3,4\},\end{cases}\\
x_{b_j}^{(z)}&=\begin{cases}\alpha,&z=j,\\B_{b_j},&z\ne j.
                         \end{cases}
\end{aligned}
\tag{NBP.15.3}
$$

Their targets are $R_0,R_0,R_1,R_2,R_3,R_4$. Every finite literal
address is constant on them, or separates the two groups
$\{0_a,1,2\}\mid\{0_c,3,4\}$ in a partner cone, or isolates $j$
in a $b_j$ cone. A specified suffix may give a constant reply even
in one of those cones. The family may be chosen for every such tuple
$B$; it is not restricted to the orbit values in Proposition 11.3.

Proof. By Proposition 9.3 either every class value is an image, or one
right value is alpha and its partner is beta. The only leaf image is
beta. Distinct classes cannot both have value beta. In the positive
case every other class is therefore a branch image; in the zero case
there is at most one beta class. This proves exhaustion, disjointness
and the targets, using the complete-row conclusion of Proposition 9.3.
Each indicated profile is attained by choosing the remaining class
values to be distinct branch images and applying that proposition's
actual inverse. There are infinitely many branch images: the distinct
orbit values $T_n$ of Theorem 3.3 belong to $\mathcal B$ for $n\ge2$.
Thus finitely many forbidden values can always be avoided.

For (NBP.15.3) all six values in each tuple are distinct. At $0_a,0_c$
they are images; at $j$ the only nonimage is alpha with its prescribed
beta partner. Proposition 9.3 constructs the actual finite inverse
origin of each filling and gives the stated whole target. This also
retains both occurrences of each repeated partner and all disequalities.
For an address shorter than three the reply is the common exterior
branch. Every other address is uniquely $p w$, $p\in P$, and the
actual occurrence identity (NBP.9.7) applies. In a partner cone it reads
either beta or the one fixed $B_d$, constant on the two groups. In a
right cone it reads alpha at $j$ and $B_{b_j}$ elsewhere. Applying any
finite suffix to these two actual trees gives either one reply or the
stated two-part partition. This includes extensions past leaves and
all absent replies. These are mathematical witness families; they do
not give the reader an additional port or restrict its full domain.
$\square$

### 15.2 Equality forces a forest and three different query classes

**Lemma 15.3 (saturated support of a successful prescribed-code table).**
Suppose a controller satisfies Definition 15.1. On each family
(NBP.15.3), the union of its actual runs is a forest of two disjoint
full binary trees, of depth at most two. It contains every installed
state: exactly three running states and exactly five halts, with one
halt $H_j$ of whole output $R_j$ for each $0\le j\le4$. The two roots
are the two different entries $\iota(0),\iota(1)$.

Both zero sources lie in the same tree. Its running states form a
chain of singleton tests for a set $S\subseteq J$, with $s=|S|\le2$.
Each singleton-positive edge halts at its own $H_j$; the continuation
ends at $H_0$. The other tree has the remaining positive leaves
$T=J\setminus S$ and $3-s$ running states. Across both trees the three
queried occurrence classes are different. A partner query can occur
only in the positive tree, at most once. If $s=0$, that tree first
queries a partner and then one right class from each of $J_a,J_c$.

Proof. Restrict the fixed controller and the original prescribed code
to one of these actual six-source families. Let $n,h,m,e$ denote the
numbers of visited running states, visited halts, distinct entries and
distinct directed successor edges in their run union. Five different
required whole rows force $h\ge5$. Reachability from the entries gives
$n+h-m\le e$, by the spanning-forest count used in Proposition 11.2.
The all-address restriction in Proposition 15.2 gives $e\le2n$ and
$m\le2$. Also $n+h\le8$. Consequently

$$
5\le h\le m+n\le2+n,\qquad n+h\le8,
\quad\Longrightarrow\quad
(n,h,m,e)=(3,5,2,6).
\tag{NBP.15.4}
$$

All eight installed states are therefore visited; there are no extra
installed states or duplicate-output halts. Each running state has two
distinct actual successors. List two entry slots and the two successor
slots of each of the three running states. Their images cover all eight
vertices by reachability. As there are exactly eight slots, their images
are pairwise different. Thus entries have no incoming edge, every other
vertex has exactly one, and every vertex is reachable from an entry.
No directed cycle is reachable under these conditions. This proves the
two-tree assertion without assuming the original four-successor table
acyclic. Every root-to-leaf path in this support is an actual run path:
each leaf is visited, and the forest has a unique path from its root.
Hence its depth is at most two.

The two zero sources reach the unique $H_0$, so they have the same
entry and the same path. A nonconstant partner query separates them;
it cannot occur on that path. A constant query has only one used
successor and is also excluded by (NBP.15.4). Each node on the zero
path must thus isolate some positive $j$ by a $b_j$-cone query. Its
positive child is immediately $H_j$: only that one actual source takes
this child, so no further full binary node can be supported there.
The other child continues the zero path. A repeated singleton query
would be constant after its positive source had left. Thus these nodes
are exactly the distinct indices of $S$, and $s\le2$.

The other tree has $4-s$ distinct positive leaves and $3-s$ running
vertices. No $b_j$ with $j\in S$ can be queried there, since its reply
is constant on these positive sources. For $s=2$ its sole running node
separates two positive sources and queries either one of their right
classes or a partner if their groups differ. For $s=1$ there are three
positive leaves and two running vertices, arranged as a root with one
halting child and one running child. A singleton at the root removes
its positive source; neither that singleton nor any removed index can
be a nonconstant child query. A partner at the root leaves each child
inside one group, where every partner query is constant. If the child
is a partner query the root was therefore a singleton. In every case
these two queried classes are different, with at most one partner.

For $s=0$ the four-leaf tree has depth at most two, so both children of
its root are running and each has two leaves. A singleton root would
leave three positive leaves for one remaining call on its other child,
which is impossible. A partner root splits $J_a\mid J_c$; each child
must query a right class in its own pair, because all partner queries
there are constant. These are three different classes. Combined with
the distinct zero-chain classes, this proves all assertions. $\square$

### 15.3 A code-preserving bridge on the successful controller

**Theorem 15.4 (root normalization with the original arbitrary code).**
For every compatible $\sigma$ of Definition 15.1 and every witnessing
controller, there is a controller with exactly the same installed states,
running/halting partition, whole halting outputs and initialization
$\iota$. Each running address is a representative $p_d$ of its actual
class. On every original $u\in\mathcal U_*$, started with the same
prescribed $\sigma(u)$, its entire state path and actual call count
are those of the original controller. In particular no new code is
chosen and no extra state or call is used.

Proof. All running addresses have length at least three by Lemma 15.3:
a shorter address is constant on its six witnesses. Write the fixed
address of running state $k$ uniquely as $p w_k$, and let $d_k$ be the
class of $p$. By that lemma the three $d_k$ are pairwise different.
Put $\ell_d=\beta$ for $d=a,c$ and $\ell_{b_j}=\alpha$.

For any six distinct $B_d\in\mathcal B$, consider the following eight
state-valued slots of the same original controller:

$$
\iota(0),\ \iota(1),\qquad
L_k=\operatorname{next}(k,r_{\ell_{d_k}}(w_k)),\qquad
V_k(B_{d_k})=\operatorname{next}(k,r_{B_{d_k}}(w_k))
\quad(k\in Q).
\tag{NBP.15.5}
$$

Each actual query in family (NBP.15.3) reads one of these two subtree
values. Lemma 15.3 says that each running state has two used distinct
successors; thus both slots at that state are used. Both entries are
used as well. The eight slots in (NBP.15.5) consequently form a
bijection onto the same installed $\mathcal K$, for every such $B$.
This conclusion does not assume any constancy of $\sigma$ on the
six root profiles: success and the tight count force both entries to
be used even when their source assignments change with $B$.

Fix a state $k$ and any two branch images $B,B'\in\mathcal B$.
Choose five other pairwise distinct branch images, avoiding both
$B,B'$, for the other classes. This is possible by Proposition 15.2.
Compare (NBP.15.5) for $B_{d_k}=B$ and $B_{d_k}=B'$, keeping those
other values fixed. The entry slots and all leaf slots are fixed.
The other two branch slots are fixed because their queried classes
are different from $d_k$. Exactly seven slots therefore have unchanged
values. Each list is a bijection onto the same eight-element set, so
the remaining slot must also have the same value. Since $B,B'$ were
arbitrary, there is one $v_k\in\mathcal K$ such that

$$
\operatorname{next}(k,r_B(w_k))=v_k
\qquad\text{for every }B\in\mathcal B.
\tag{NBP.15.6}
$$

Replace the address at $k$ by $p_{d_k}$ and install the fixed table

$$
\begin{aligned}
\operatorname{next}'(k,\mathsf{branch})&=v_k,\\
\operatorname{next}'(k,\ell)&=
       \operatorname{next}(k,r_\ell(w_k))\quad(\ell=\alpha,\beta),\\
\operatorname{next}'(k,\mathsf{absent})&=H_0.
\end{aligned}
\tag{NBP.15.7}
$$

Keep the original $\iota$ and halt outputs. The three equations specify
all four successors. On an arbitrary actual source, its class value
$x_{d_k}$ is either alpha, beta or a branch image by Proposition 15.2.
For a leaf, (NBP.15.7) gives exactly the old successor by the occurrence
identity. For a branch image, (NBP.15.6) does so. Representative roots
are reached on the entire fiber, so the absent entry is unused.
Both executions start at $\iota(\sigma(u))$. Induction along the
original terminating run now gives equal next states at every running
visit, one actual invocation on each side, and the same final whole-row
halt. This holds for every $u$, without changing its code.

The comparison varied actual witness sources to constrain one fixed
table. It did not demand preservation of $\sigma$ under a deep padding
operation, or infer the code of any source from one representative.
The new addresses and reply table are installed constants, with no
runtime address calculation. Replies and literal words need not be
identical between the two controllers; state paths and paid calls are.
$\square$

### 15.4 Structural classification of all prescribed binary codes

**Theorem 15.5 (full-fiber compatibility criterion).** A prescribed
$\sigma$ of Definition 15.1 is compatible if and only if there is
$z\in\{0,1\}$ with the following properties:

1. $\sigma$ is identically $z$ on $Z_a\cup Z_c\cup Z_*$.
2. On each entire $\Pi_j$ it is a constant $\varepsilon_j$.
3. With

$$
\begin{aligned}
S&=\{j\in J:\varepsilon_j=z\},\qquad T=J\setminus S,
       \qquad s=|S|,\\
W&=\{j\in J:\text{there exists }u\in Z_{b_j}
                              \text{ with }\sigma(u)\ne z\},
\end{aligned}
\tag{NBP.15.8}
$$

   one has

$$
s\le2,\qquad W\subseteq T,\qquad
|W|\le1+\mathbf1_{\{s=1\}}.
\tag{NBP.15.9}
$$

In particular the code on a permitted $Z_{b_j}$, $j\in W$, may vary
arbitrarily with acquired finite structure. The criterion quantifies
over every member of these actual fibers. Testing one source per profile
is insufficient for an arbitrary prescribed code. Every compatible code
actually uses both values, needs exactly eight states under this budget,
and can be served by three running states and five whole-row halts.

Proof, necessity. Apply Theorem 15.4, preserving $\sigma$ and $\iota$,
and restrict the resulting root controller to any family (NBP.15.3).
Use its two-tree structure from Lemma 15.3. Denote the code of the
zero tree by $z$. This tree is a chain on $S$, ends at $H_0$, and
has the positive leaves $H_j$, $j\in S$, with $s\le2$. The other tree
contains precisely the positive leaves indexed by $T$.

Consider starting the positive tree on a root profile with no right
alpha, and with partner roots either those of $Z_a$, those of $Z_c$,
or both branches. Every right-class test then follows its branch edge.
At a partner test the two children contain nonempty sets of positive
candidates, since both support edges are used. Either possible partner
reply therefore chooses a nonempty set. There is at most one such test
by Lemma 15.3. At every subsequent right test its branch edge retains
at least one positive candidate. Thus all these runs stay within the
positive tree and end at a positive halt, not $H_0$. This argument
includes a positive tree with no partner test. Starting the zero tree
on any of these profiles follows its chain to $H_0$. Since the normalized
table depends only on roots, every source of $Z_a,Z_c,Z_*$ must have
code $z$. This proves property 1 on the entire three fibers.

If $j\in T$, its positive root profile follows the zero chain to
$H_0$ when started there, because every tested singleton belongs to $S$.
So all of $\Pi_j$ must use the other code. If $j\in S$, the positive
tree has no $b_j$ query, and its run on that profile agrees with the
no-right-alpha profile having the same partner roots. The preceding
paragraph shows that it ends at a positive $T$-halt. It cannot return
$R_j$. Hence all of $\Pi_j$ must use $z$. This proves property 2
and identifies the same $S$ in (NBP.15.8), rather than a set sampled
from six sources.

Let $P_*$ be the state path from the other entry on the all-branch
profile $Z_*$. As just proved, it ends at a positive halt in at most
two calls. If $j\in W$, some actual source in $Z_{b_j}$ starts at
this same entry and must return $R_0$. Its root profile differs from
the all-branch profile only by beta at $b_j$. Its run can deviate from
$P_*$ only if a state on $P_*$ queries $b_j$. Therefore

$$
W\subseteq\{j:\text{a state on }P_*\text{ queries }b_j\}
\subseteq T.
\tag{NBP.15.10}
$$

For $s=2$ the positive tree has one running state, so this set has
size at most one. For $s=1$ its two running states give size at most
two. For $s=0$, Lemma 15.3 forces a partner first and one right-class
query second on $P_*$, giving size at most one. These are exactly
(NBP.15.9). Both code values are attained on the witness family; the
state count and necessity of eight follow from Lemma 15.3.

Proof, sufficiency on every actual source. Assume properties 1--3.
Install the five halts $H_j$ with their fixed whole outputs $R_j$.
Every right test below queries the literal root $p_{b_j}=q_jR$.
Its alpha successor is $H_j$, its beta successor is $H_0$, and its
absent successor is $H_0$. Its branch successor is specified below.
Thus every test has a total four-reply table. The absent successor is
unreachable at these representatives, but is installed and fixed.

For $s=2$, write $S=\{i_1,i_2\}$ and $T=\{k,l\}$, choosing $k$
so that $W\subseteq\{k\}$. At entry $z$, test $i_1$ and then $i_2$
on the branch continuations, the final branch going to $H_0$.
At the other entry, test $k$, with branch successor $H_l$.

For $s=1$, write $S=\{i\}$ and choose distinct $k,l\in T$ with
$W\subseteq\{k,l\}$; let $m$ be the remaining member of $T$.
At entry $z$, test $i$ with branch successor $H_0$. At the other
entry, test $k$ and then $l$ on the branch continuation, with the
final branch successor $H_m$.

For $s=0$, entry $z$ is $H_0$ itself. At the other entry first query
a partner. If $W$ has an element $w\in J_a$, query $c$; otherwise
query $a$. A beta reply selects the positive pair belonging to that
partner, and a branch reply selects the other positive pair. Install
one right-class test in each pair, with branch successor the halt of
the other index in that pair. If $W=\{w\}$, choose $w$ as the
right-class test in its pair. The chosen partner ensures that an
all-branch partner profile enters that pair. The partner's alpha and
absent successors are fixed to $H_0$.

These constructions use exactly three running states and five halts,
with two different entries, and at most two actual calls on every
required run. On $\Pi_j$, the prescribed entry is the one containing
$j$; the unique right alpha and the forced partner beta give exactly
$H_j$. On any zero profile, entry $z$ follows only branch or beta
edges to $H_0$, or already is $H_0$. A zero source using the other
entry must belong to $Z_{b_j}$ for $j\in W$. In the first two
constructions its path tests that $j$ and takes its beta edge to $H_0$.
In the third its partner is a branch, so it reaches the pair containing
$w=j$, tests $j$, and takes the same beta edge. This verifies every
source in the exhaustive partition of Proposition 15.2, including
both codes within any permitted $Z_{b_j}$.

Only the fixed original $\sigma$ is exported; its two distinct entry
states recover it at entry. There is no retained copy of it after
initialization. Representative-address reading and Proposition 9.3's
whole-row target identity make these common native controllers on the
entire $\mathcal U_*$. Every $H_j$ already contains the complete repaired
exterior, the canonically renamed restricted partition, its equalities
and disequalities and the absent-cut guards, including the surviving
old occurrence of a repeated partner. The six sources are used only
for necessity. $\square$

### 15.5 Consequences, a strict state penalty and the padding boundary

**Corollary 15.6 (root codes, target codes and genuine value dependence).**
For a prescribed code determined by the class roots, Theorem 15.5 is
a finite structural classification: use its constant value on each
$Z_d,\Pi_j,Z_*$ in (NBP.15.8). For a prescribed binary function of the
whole target alone, compatibility is equivalent to the block containing
$R_0$ containing at most two of $R_1,\ldots,R_4$.

Compatible prescribed codes need not be functions of the root profile.
For example, let $E=\langle\beta,\alpha\rangle$ and prescribe

$$
\sigma(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{x_a=E\}},&u\in Z_{b_3},\\
0,&u\in Z_a\cup Z_c\cup Z_*\cup Z_{b_1}\cup Z_{b_2}\cup Z_{b_4}.
\end{cases}
\tag{NBP.15.11}
$$

This code is compatible, and takes both values within the same whole
root fiber $Z_{b_3}$.

Proof. In the root-code specialization the quantities in Theorem 15.5
are exactly those constant profile values; no representative selection
is used. A target code has the same value $z$ on every zero profile,
so $W=\varnothing$, and the only additional restriction is $s\le2$.
For (NBP.15.11), $z=0$, $S=\{1,2\}$, $T=\{3,4\}$ and $W=\{3\}$.
Both values on $Z_{b_3}$ are attained: set $x_{b_3}=\beta$ and take
$x_a=E$ or a different branch image, filling the other classes by
distinct branch images avoiding these values. Proposition 9.3 gives
actual origins with these same roots. Equality with $E$ is a finite
comparison on an acquired term, not an extra query service. Thus the
code is lawful under the stated acquisition premise and satisfies
(NBP.15.9). The theorem supplies its full-fiber upper. $\square$

**Theorem 15.7 (the acquired partner-beta bit has a sharp nine-state cost).**
Prescribe the acquired code

$$
\sigma_a(u)=\mathbf1_{\{x_a=\beta\}}.
\tag{NBP.15.12}
$$

Among the controllers of Definition 11.1 with this same code and at
most two actual calls, the least total installed state count is nine.
The exclusion of eight allows every finite literal address and all
four native replies, with no tree-shaped controller assumption.

Proof. In every family (NBP.15.3), the two zero sources have different
$\sigma_a$ values. Lemma 15.3 forces their entries to coincide for
any successful controller with at most eight states. It also forces
the two code entries to be different, a contradiction. Thus every
such controller needs at least nine states. This lower argument does
not rely on a particular known eight-state initializer failing to
factor through $\sigma_a$. Indeed the same exclusion holds with
any finite call bound: the counting and unique-zero-halt part of
Lemma 15.3 does not use its two-call depth assertion.

For the two-call upper install four running states $B_1,\ldots,B_4$
querying $p_{b_1},\ldots,p_{b_4}$, and the five whole-row halts $H_j$.
Entry $1$ is $B_1$, with its non-alpha successor $B_2$; entry $0$ is
$B_3$, with its non-alpha successor $B_4$. Each $B_j$ takes alpha to
$H_j$; $B_2,B_4$ take every non-alpha reply to $H_0$. These rules
specify all four successors. If $x_a=\beta$, Proposition 9.3 allows
only targets $0,1,2$. If $x_a\ne\beta$, it allows only $0,3,4$,
since either positive $1,2$ would force $x_a=\beta$. Each two-test
chain therefore returns the correct whole row on every actual source.
This reuses the right-test chains of Proposition 11.5 with entry
selected by the prescribed acquired bit. All nine states count and
no additional source field survives initialization. $\square$

**Proposition 15.8 (arbitrary codes do not admit universal deep padding).**
Theorem 15.4 does not follow by requiring every attained root-profile
and prescribed-code pair to have representatives whose branch values
have arbitrarily large minimum leaf depth. That requirement is false
on the same entire native fiber.

Proof. Prescribe the lawful acquired-term code
$\chi(u)=\mathbf1_{\{x_a=E\}}$. The all-branch profile has an actual
code-one source: take $x_a=E$ and five distinct other branch images.
Proposition 9.3 supplies its origin. Every source with that same code
has $x_a=E$, whose minimum leaf depth is one. Hence for every $L\ge1$
there is no representative preserving that profile and code for which
all branch classes have minimum leaf depth greater than $L$.
This refutes that proposed padding property alone. It neither forbids
other controllers for a prescribed code nor contradicts Theorem 15.4,
which constrains a controller already successful at the tight budget
by (NBP.15.5), without preserving codes under source replacement.
$\square$

### 15.6 Suppliers and the exact remaining scope

**Convention 15.9 (attribution and limits).** Definitions 1.1--1.2,
Definition 9.1 and Proposition 9.3 supply the original trees, update,
full actual inverse fiber and all five complete canonical targets.
Their project-source interfaces are
[NativeClassRootImage](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.lean),
[NativePredecessorRowRecovery](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.lean)
and [NativeWholeRowPlan](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan.lean).
The chart, whole-target and representative-read bridges of §§10--12
are credited suppliers, including their all-source quantifiers.
Proposition 11.3 and
[NativeSixSourceCones](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.lean)
supply the fixed six-source occurrence geometry; Proposition 15.2
proves the additional freedom to replace its six branch values.

Proposition 11.2's reachable-graph count and its mature spanning-forest
argument are reused in (NBP.15.4). The new deductions are the equality
forest and different queried classes, the single-slot comparison
(NBP.15.5)--(NBP.15.6), and the resulting fixed-code all-fiber criterion.
Proposition 11.5 supplies the right-test chain bodies used for the
nine-state upper, while the universal eight-state exclusion for the
prescribed partner bit is the additional lower conclusion here.

The jointly optimized frontier of Theorem 11.6 and
[NativeRepeatedPartnerFrontier](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier.lean)
permits reselection of encoder and controller. The existing
[NativeFiniteRootMinimax](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteRootMinimax.lean)
and Theorem 12.3 do not preserve an arbitrary supplied encoder:
(NBP.12.7) chooses the code of a representative. They are not used to
assert the prescribed-code upper here. Theorem 15.4 instead preserves
one successful table's original code and initialization on every source.
Its comparison uses the exact eight-slot saturation; with spare states,
more code values or different call budgets the different-class argument
and single remaining slot need not hold. No general prescribed-code
frontier is obtained.

The classification is a statement about entire actual source fibers,
not an effective decision method for an arbitrary supplied computation
$\kappa$. Establishing its universal constancy and existence conditions
for such a computation is a separate task. The natural root-code and
target-code families in Corollary 15.6 are consequences, not restrictions
silently imposed on Theorem 15.5. General code-preserving deep padding
remains unavailable, as Proposition 15.8 shows.

These are repository-derived ordinary mathematical deductions relative
to the cited suppliers. Decision-support graph counting and finite
case analysis are elementary intermediates; no external asymptotic
bound or numerical frontier is imported. The different late-target
native pressure/template results, binary-XOR problems, K-bonacci
problems, graph problems and quantum problems supply no numerical
premise here. No worldwide-priority or current kernel-verification
claim is made. The budgets count actual reader calls and all installed
abstract states. Acquisition, acquired-term computation, representation
of addresses and tables, fixed whole-output storage, export, lawful
entry, isolation, authentication and physical realization retain their
separate conditions and prices.

## 追加锚（本行以下为增补区）
