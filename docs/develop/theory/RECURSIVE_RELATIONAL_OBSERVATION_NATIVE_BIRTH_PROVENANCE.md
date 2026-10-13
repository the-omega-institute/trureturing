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
