# Native alpha/beta recutting and conditional row memory

## 1. Native source, fixed cut and retained information

**Definition 1.1 (source and address port).** Use the actual finite nonempty ordered
tree algebra from [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
`Source := FreeMagma Bool`, with `true` denoting $\alpha$ and `false` denoting
$\beta$. Its native `substitution` is the homomorphic map

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{NAR.1.1}
$$

Addresses are finite words in $L,R$, with root $\varepsilon$; $L$ corresponds to
`false` and $R$ to `true` in the native address list. Write $a\preceq p$ for
the prefix relation, $\operatorname{Pos}(u)$ for actual node addresses and
$u|_p$ for an existing subtree. The native
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
`readout` returns precisely

$$
r_u(p)\in\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}.
\tag{NAR.1.2}
$$

It reports the root constructor when the address ends, descends through a
branch according to the next letter, and reports absence if a nonempty suffix
remains at a leaf. Every finite address is a legal query, including absent
addresses. Pairing, labels, order and occurrences are literal; no equations
identify different trees.

**Definition 1.2 (the supplied complete row).** Fix a finite prefix-free public
cut $P$, allowing $\varnothing$ and $\{\varepsilon\}$. Reuse
[Sparse Literal History Transport, Definition 59.1](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md):
$O=I_P(u)=P\cap\operatorname{Pos}(u)$, and $C=C_P(u)$ is obtained by replacing
each entire subtree at $p\in O$ by an address-marked hole $\square_p$.
The concrete exterior retains every remaining label and bracket.
The relation $\pi$ is the complete partition

$$
p\sim_\pi q\quad\Longleftrightarrow\quad u|_p=u|_q
\qquad(p,q\in O),\qquad R_P(u)=(C,\pi).
\tag{NAR.1.3}
$$

In particular, distinct classes mean disequality. The hole addresses are
readable from $C$; every $p\in P\setminus O$ is blocked by a concrete strict
prefix leaf of $C$. Let $B=O/\pi$ and $k=|B|$. Order classes by their least
address in the lexicographically ordered hole list, independently of their
values. Let $p_b$ be the least address in class $b$ and $z_b=u|_{p_b}$.

This is exactly the information in
[ActualCutPartitionDecoder](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean),
`literalRecord`, and its `canonicalRow_record_iff`; canonical row syntax
and $(C,\pi)$ are interchangeable. The full row fiber is the supplied
[Sparse History Theorem 59.4](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md)
and [NativeCutFibers](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean),
`legal_values_row` and `rowFiberEquiv`:

$$
\mathcal U_R
=\{u:R_P(u)=R\}
=\{C[(z_{[p]})_{p\in O}]:
       z_b\in\mathcal T,\ b\ne c\Rightarrow z_b\ne z_c\}.
\tag{NAR.1.4}
$$

The fillings are a bijective parametrization, including the empty tuple.
This supplier, rather than a promise that hidden values can be compared,
justifies the alternative sources used below.

**Definition 1.3 (birth sets and alpha label).** For a realized exterior $C$ set

$$
\begin{aligned}
L_C&=\{aL\in P:C\text{ has a concrete }\beta\text{ leaf at }a\},\\
D_C&=\{aR\in P:C\text{ has a concrete }\beta\text{ leaf at }a\}.
\end{aligned}
\tag{NAR.1.5}
$$

The letter $D$ denotes right births, and is unrelated to the class set $B$.
Define the alpha label

$$
A_P(u)=
\begin{cases}
b,&z_b=\alpha\text{ for some }b\in B,\\
\bot,&z_b\ne\alpha\text{ for every }b\in B.
\end{cases}
\tag{NAR.1.6}
$$

Distinct class values ensure uniqueness. The semantic symbol $\bot$ is a
label for no alpha class, not an absent-address reply. It is not a query
answer supplied with a literal row.

**Definition 1.4 (conditional augmentation).** Use a common symbol $*$ for an
omitted supplement and define

$$
S_P(u)=
\begin{cases}
(R_P(u),A_P(u)),&L_{C_P(u)}\ne\varnothing,\\
(R_P(u),*),&L_{C_P(u)}=\varnothing.
\end{cases}
\tag{NAR.1.7}
$$

All record equalities below use this conditional convention. Common cut,
class naming and source-independent controls are understood. If additional
source information is retained, its actual nonempty fiber is declared
explicitly; it is not silently replaced by $\mathcal U_R$.

## 2. Exhaustive old/new-hole collisions

**Theorem 2.1 (native one-step collision classification).** For every
$u\in\mathcal T$ and fixed finite prefix-free $P$, the next reached holes are

$$
I_P(\rho u)=O\sqcup L_C\sqcup D_C.
\tag{NAR.2.1}
$$

The next concrete exterior $C^+=C_P(\rho u)$ is a finite function of $P,C$
alone. Old hole $p$ has value $\rho z_{[p]}$; every hole in $L_C$ has value
$\beta$ and every hole in $D_C$ has value $\alpha$. The complete next
partition is given by the following exhaustive table, with symmetric cases
understood.

| Pair of next holes | Equality condition |
| --- | --- |
| Old $p$, old $q$ | $p\sim_\pi q$ |
| Left birth, left birth | Always |
| Right birth, right birth | Always |
| Left birth, right birth | Never |
| Old $p$, right birth | Never |
| Old $p$, left birth | $A_P(u)=[p]$ |

Moreover the alpha label of the next row is precisely

$$
A_P(\rho u)=
\begin{cases}
[D_C]_{\pi^+},&D_C\ne\varnothing,\\
\bot,&D_C=\varnothing,
\end{cases}
\tag{NAR.2.2}
$$

where $[D_C]_{\pi^+}$ denotes the single canonically named next class
containing all right births.

**Proof.** Reuse [Transport--Memory Completion, Proposition 22.2,
(RA.2205)--(RA.2207)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md):
old addresses persist with subtree $\rho(u|_p)$; the only new addresses are
the two children of an old beta leaf; $\rho$ is injective and has no alpha
leaf in its image. A beta leaf strictly inside an old hole cannot produce
a public cut address, since that address would strictly extend another
element of $P$. Thus every new reached public cut comes from a concrete
beta leaf of $C$, giving exactly (NAR.2.1). The birth sets are disjoint from
each other and from $O$, by their last letters and by the node-birth supplier.

To compute $C^+$, leave old holes opaque, replace each concrete alpha leaf
by beta, replace each concrete beta leaf at $a$ by
$\langle\beta,\alpha\rangle$, and replace a new child by a hole exactly when
its address lies in $P$. Keep all other brackets and concrete children.
Prefix-freeness excludes any additional cut inside an opaque old hole or
below a newly cut child. The supplier says no other address can become
reached in one step. This finite construction therefore yields the actual
exterior and every still-blocked cut guard.

The supplied injectivity preserves precisely the old partition, including
its disequalities. In addition to the supplied image exclusion,
the native constructor equations immediately give

$$
\rho t\ne\alpha,\qquad
\rho t=\beta\quad\Longleftrightarrow\quad t=\alpha.
\tag{NAR.2.3}
$$

Indeed alpha maps to beta, beta maps to a branch, and a branch maps to a
branch. The old values are exactly these images. Comparing them with the
two literal birth values proves all six rows of the table. Each reached
hole is in one of the three sets, so there is no unclassified pair.
Only right births can have value alpha, which proves (NAR.2.2).
The class named there is obtained from the computed partition and its
least occurrence, rather than from a hidden subtree comparison. $\square$

**Definition 2.2 (finite closed update).** On a realized $S=(R,m)$ compute
$L_C,D_C,C^+$ as in Theorem 2.1. Copy the old classes, add one common left
class when $L_C$ is nonempty and one common right class when $D_C$ is
nonempty, and merge the left class with old class $m$ exactly when
$L_C\ne\varnothing$ and $m\in B$. If $L_C$ is empty no old alpha label is used.
Sort all reached addresses and rename the resulting classes by their first
occurrences. Compute $a^+$ by (NAR.2.2), and retain it only if
$L_{C^+}\ne\varnothing$. Denote the resulting augmented finite record by
$\operatorname{Step}_P(S)$. All operations are on the retained finite
exterior, partition and, when needed, alpha label.

## 3. Closure and recovery of the future row procedure

**Theorem 3.1 (effective closure and exact conditional distinction).** For every
finite source $u$,

$$
S_P(\rho u)=\operatorname{Step}_P(S_P(u)).
\tag{NAR.3.1}
$$

For every pair $u,v$ with the same current row $R=(C,\pi)$,

$$
\begin{aligned}
&\forall n\ge0,\ R_P(\rho^n u)=R_P(\rho^n v)\\
&\quad\Longleftrightarrow\
R_P(\rho u)=R_P(\rho v)\\
&\quad\Longleftrightarrow\
\bigl(L_C=\varnothing\ \text{or}\ A_P(u)=A_P(v)\bigr).
\end{aligned}
\tag{NAR.3.2}
$$

Thus a left birth makes the old alpha label exactly the missing distinction;
without a left birth that distinction is unnecessary even for all later
same-$P$ rows.

**Proof.** Theorem 2.1 and the canonical renaming in Definition 2.2 prove
(NAR.3.1). If $L_C$ is empty, the first next row is independent of the
discarded old alpha label. In either case, its alpha label is known from
the right births, so its conditional augmentation is also determined.
Iteration proves sufficiency for every finite $n$ by induction.

For necessity when $L_C$ is nonempty, choose one left birth $\ell$.
For each old class $b$ compare $\ell$ with $p_b$ in the next partition.
It is linked exactly when $A_P(u)=b$. Consequently two different class
labels, or a class label and $\bot$, give different next partitions.
If there are no old classes, both labels must be $\bot$ and this implication
is vacuous. Equality of all future rows implies equality at $n=1$.
These observations prove both equivalences. $\square$

The generic greatest stable-core construction is supplied by
[Atlas Stable Core Holonomy, Theorem 2.1 and Mathematical Citation 2.2](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md).
Here (NAR.3.2) computes its row-level future distinction for this particular
source, fixed cut and substitution. It does not identify that kernel with
the kernel for all native queries or for a larger action menu.

**Definition 3.2 (finite-epoch response representation).** A future-row
representation of $u$ is a finite description of a procedure which, for
each requested integer $n\ge0$, terminates and returns the entire
$R_P(\rho^n u)$. Representations are compared by the rows they return,
not by equality of program syntax. A finite list of requests need not
be chronological. Such a description is not an infinite stored list
of rows, an executed update sequence, or an archive of actual read events.

**Theorem 3.3 (augmented row, two rows and all future rows).** On realizable
records there are effective recoveries

$$
S_P(u)
\ \longleftrightarrow\
\bigl(R_P(u),R_P(\rho u)\bigr)
\ \longleftrightarrow\
\bigl(n\longmapsto R_P(\rho^n u)\bigr),
\tag{NAR.3.3}
$$

where the last expression is interpreted as Definition 3.2. The record
recoveries are inverses on their actual images; recovery of a procedure
is inverse up to agreement on every finite-epoch response.

**Proof.** From $S_P(u)$ project $R_P(u)$ and perform one finite update to
obtain $R_P(\rho u)$. Conversely, suppose the ordered pair of rows is
realized by one source. Compute $L_C$ from its first exterior. If it is
empty, return $(R,*)$. Otherwise take the least left-birth address $\ell$.
In the second complete partition inspect its equality links with the old
representatives $p_b$, whose addresses remain reached. Return the unique
linked class $b$ if there is one, and $\bot$ if there is none.
Theorem 2.1 proves uniqueness, truth and completeness of this test.
There is no query to an unknown value in this reverse map: its inputs
already contain the partition. For $k=0$ the empty test returns $\bot$.

From an augmented record supply the procedure that, on input $n$, applies
$\operatorname{Step}_P$ exactly $n$ times and projects the resulting row.
Every intermediate record is realized by $\rho^j u$, by (NAR.3.1).
Each finite operation terminates, and induction proves the requested
response. From any correct future-row procedure, request only epochs
zero and one and use the preceding reverse map. These requests evaluate
the given representation; they are not native source reads.
Starting with either realized finite record, the compositions return that
same record. Starting with a response procedure, the regenerated procedure
returns the same row for each $n$; no claim of equal code follows.

This argument establishes the infinite universal statement by finite
induction and supplies one finite response description. It does not
replace that description by an already executed infinite archive.
Nor does it recover the source, a predecessor record, arbitrary queries,
or events of an execution. $\square$

## 4. The producer must retain the distinction before the access cut

**Assumption 4.1 (truthful acquired producer data).** Before access to acquired
values is cut, the actual producer still possesses either a lossless acquired
tree $u$, or the row $R_P(u)$ together with one truthfully acquired finite
subtree $z_b$ at a declared representative of every old class.
The retained values belong to this same source and version. A merely
feasible filling selected from (NAR.1.4) is not such data.
Local traversal and equality of acquired finite terms are allowed
computations; no equality oracle for unknown subtrees is supplied.

The actual full-tree supplier is
[NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean),
`Control.deliver`, `sourceControl` and `native_source_producer`.
Its terminal control carries the acquired tree and an empty continuation
stack; its acquired values are built from truthful replies, while the
register stays at epoch zero. This is the lossless source used in
[Sparse History Definition 59.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md),
before that definition's value-forgetting handoff.
[ActualCutPartitionRecovery](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionRecovery.lean),
`classValue_at`, supplies the mathematical value correspondence when the
source is available; it is not additional access after forgetting.

**Theorem 4.2 (producer-owned zero-new-query extraction).** Under Assumption 4.1
the producer can compute $S_P(u)$ with no additional native source queries,
and retain its required label before the complete access cut. A handoff
which actually exports this augmented record, and whose later accessible
state contains no further source distinctions, permits the finite row
calculations of Theorems 3.1 and 3.3 without new source queries.
For a partial producer whose complete accessible input is only the
projected row, zero-query extraction of the needed label is impossible
when a left birth exists and two old alpha labels remain feasible.

**Proof.** First compute $L_C$. If it is empty the supplement is $*$.
Otherwise inspect the root constructor of each acquired representative
value: exactly the value $\alpha$ is the alpha leaf, and every other value
is beta or a branch. Pairwise distinct values permit at most one positive
test. Record its canonical old class, or $\bot$ if all tests are negative.
When the acquired object is the full tree, navigate its finite syntax to
each $p_b$ to obtain these same values. All information used is already
present at the producer; the inspection makes no native read.
Writing the resulting label into the payload before dropping access
preserves precisely Definition 1.4. Theorem 3.1 then uses only that payload
and common $P$; Theorem 3.3 supplies the future response procedure.
This is conditional on the stated retention and handoff.

A partial producer whose accessible information is only $R$ cannot
manufacture the required label by such a computation when $L_C$ is
nonempty and two alpha labels remain feasible. Its accessible state is
the same for sources with those different labels, so a deterministic
zero-query extraction returns the same label and is wrong on one source.
The native pair (NAR.6.2) supplies such sources. It must preserve truthful
distinguishing acquired data before the cut, or obtain information through
a separately supplied read service; projected syntax alone does not
provide it. $\square$

**Definition 4.3 (access and operation boundary).** The complete handoff used
here has the meaning of
[Sparse History Assumption 59.3 and Assumption 62.1](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).
Every accessible source-dependent field is included in the retained
input. Old acquired trees, representatives, traces, comparison tables,
pointers, source-dependent control, lengths, meters and timing are absent
as extra inputs unless explicitly retained and used to restrict the
fiber. Source continuity does not reveal a source identity label.
An inaccessible old archive can have existed without being an input.

A literal row alone does not supply Assumption 4.1. Neither does citing
[NativeEffectiveSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.lean),
`sourceName` or its semantic, non-effective `sourceDecoder`, establish
that a recipient holds decoded acquired representative values.
An actually acquired lossless name can carry information, but an effective
access path from that representation to the required finite values is
a separate premise. Theorem 4.2 uses actual producer-owned finite data,
not that semantic inverse.

The retention conclusion asserts a finite computation from those data and
the consequence of exporting its result. It asserts no existing transition
which automatically carries that marker out of the stopped producer.
The original static `Policy` returns a query or Boolean answer and keeps
one source fixed during `execute`. The stationary
[NativeWholeRowService](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowService.lean)
`controller` likewise selects queries or a row return.
Neither receives an $\mathsf{ApplyRho}$ action from this theorem.
The effective full-source selector's `selector_no_update` also excludes
that action from its acquisition run.

A physical serial interpretation separately assumes the
[Sparse History contract 1.3, entry 25.1 and version contract 32.1](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md):
a legal new entry when needed, actual same-register updates, authenticated
versions, stationary read phases, and version-indexed raw evidence.
[NativeSerialMachine](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean),
`Op.applyRho`, `nativeStep` and `Run.update`, describe the separate
serial operation. Algebraic iteration in §3 needs no execution premise.
Actual updates, re-query access, entry and authentication require this
separately supplied contract; a stopped acquisition is not resumed by
a mathematical recurrence.

## 5. Exact conditional supplemental state count

**Definition 5.1 (actual retained fiber and supplement).** Fix a realized
$R=(C,\pi)$ and all other actually accessible retained inputs $h$.
Let $\varnothing\ne\mathcal U\subseteq\mathcal U_R$ be exactly their
compatible source set and put

$$
M_{\mathcal U}=\{A_P(u):u\in\mathcal U\}\subseteq B\cup\{\bot\}.
\tag{NAR.5.1}
$$

A supplement is an additional source-dependent state $\sigma(u)$ retained
from acquired evidence, from which a common decoder with inputs $P,R,h$
computes the next whole row, or equivalently the future-row responses,
without new source information. Its conditional state count is the number
of values of $\sigma$ actually used on $\mathcal U$.
This definition counts only the supplement, not the existing row or $h$.

**Theorem 5.2 (conditional minimum).** The minimum supplemental state count is

$$
m(R,\mathcal U)=
\begin{cases}
1,&L_C=\varnothing,\\
|M_{\mathcal U}|,&L_C\ne\varnothing.
\end{cases}
\tag{NAR.5.2}
$$

On the full unrestricted row fiber,

$$
M_{\mathcal U_R}=B\cup\{\bot\},\qquad
m(R,\mathcal U_R)=
\begin{cases}
1,&L_C=\varnothing,\\
k+1,&L_C\ne\varnothing.
\end{cases}
\tag{NAR.5.3}
$$

These formulas include $k=0$. A conditional fixed-width binary supplement
requires exactly $\lceil\log_2 m(R,\mathcal U)\rceil$ bits.
Extraction without extra queries has the producer-data condition of §4.

**Proof.** With no left birth, Theorem 3.1 gives one common sufficient
supplement; a nonempty domain cannot use zero states.
With a left birth, sources with different feasible alpha labels have
different next rows by Theorem 3.1. They therefore cannot share a
supplemental state with the same $P,R,h$. This gives the lower bound
$|M_{\mathcal U}|$. Retaining the feasible alpha label attains it and,
by the same theorem, determines all future rows. This is a count on the
actual retained fiber, with all its joint restrictions.

For the full fiber, let $c_0=\beta$ and
$c_{j+1}=\langle\beta,c_j\rangle$. These are mutually distinct non-alpha
finite trees. Assign distinct members to every old class to realize
$\bot$. For any $b\in B$, assign $\alpha$ to $b$ and distinct $c_j$ to
all other classes. The supplied legal-filling bijection (NAR.1.4) realizes
the same row and label $b$. There are no other possible labels by
Definition 1.3. For $k=0$ only the empty filling and label $\bot$ exist.

A fixed-width string of length $d$ has $2^d$ configurations, so at least
$m$ configurations require $d\ge\lceil\log_2 m\rceil$. Naming the finite
feasible labels in canonical order gives a code of that length.
For an arbitrary declared $\mathcal U$, this cardinal minimum presupposes
that its feasible alphabet is specified to the decoder; it does not
supply a feasibility algorithm for arbitrary kinds of extra information.
The full-fiber code is explicit from $R$, and §4 computes its actual
label from acquired values. $\square$

The finite cardinal comparison reuses
[CompletionStateCardinality](../../../D5/S3/ObserverMemory/Prediction/CompletionStateCardinality.lean),
`completion_state_cardinality_mono`: a sufficient finite supplement maps
onto the feasible next-row image and cannot have fewer elements.
The native work is identifying that image by the conditional alpha labels
and supplying the source-level recurrence and acquired extraction,
not a new general finite-state counting principle.

For finite truthful literal constraints
$H=((n_j,q_j,c_j))$, the exact joint fiber and its effective feasibility
test are supplied by
[Sparse History Theorems 60.2 and 61.1](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).
Their existing test also determines the finite feasible alphabet in
(NAR.5.1): label $b$ is feasible precisely when adding the constraint
$(0,p_b,\alpha)$ leaves a nonempty joint fiber. The label $\bot$ is feasible
precisely when at least one simultaneous choice of replies beta or branch
at all $(0,p_b)$ leaves a nonempty fiber. There are finitely many such
choices; $k=0$ gives the empty choice. These are feasibility constraints,
not invented read events or selected fillings asserted to be the actual
source. No new general solver is needed for this restricted computation.

**Theorem 5.3 (extra history can remove the full-fiber cost).** Take
$P=\{LL,R\}$, $C=\langle\beta,\square_R\rangle$, and its one-class
partition. On its full row fiber $L_C=\{LL\}$, $k=1$ and both labels
$[R],\bot$ are feasible. If the true old reply $(0,R,\mathsf{branch})$
is also retained, the nonempty retained fiber has only label $\bot$.
Its next whole row and all future same-$P$ rows need one supplemental
state and zero new source queries.

**Proof.** The fiber consists of $\langle\beta,z\rangle$ with arbitrary
$z\in\mathcal T$. Alpha realizes $[R]$ and beta realizes $\bot$.
The retained branch reply forces $z$ to be a branch, hence not alpha;
for example $z=\langle\alpha,\alpha\rangle$ witnesses nonemptiness.
Theorem 5.2 gives one state and Theorem 3.1 computes the response procedure.
Obtaining and retaining the extra reply are premises, not free operations.
The example prevents transferring a full-fiber query lower bound to all
history restrictions. $\square$

## 6. All-source cut geometry

**Definition 6.1 (geometry condition).** For a fixed finite prefix-free cut put

$$
G(P):\quad
\forall a,\quad aL\in P\ \Longrightarrow\
                  \forall q\in P,\ a\preceq q.
\tag{NAR.6.1}
$$

Only parents of addresses ending in $L$ need be inspected, so this is
a finite, effective condition on the public cut.

**Theorem 6.2 (exact all-source row-only maintenance criterion).** The following
are equivalent:

1. $G(P)$.
2. There is a common effective finite-row function $F_P$ such that
   $R_P(\rho u)=F_P(R_P(u))$ for every $u\in\mathcal T$.
3. A current row alone determines every future same-$P$ row, effectively
   in the finite-epoch response sense of Definition 3.2.

Under the complete row-only handoff and separately supplied operation
conditions, these are also equivalent to zero-new-query next-row service
on every finite native source.

**Proof.** Suppose $G(P)$. If a row has a left birth at $aL$, the concrete
beta leaf at $a$ blocks every cut strictly below $a$. Condition $G(P)$
puts every $q\in P$ below $a$, and $q=a$ is impossible since it would
be a prefix of $aL\in P$. Thus there were no reached old holes: $k=0$.
The only old alpha label is then $\bot$. If the row has no left birth,
no label is needed. In both cases Theorem 2.1 computes the next row
from the current row alone. It also computes the next alpha label from
right births; Theorem 3.1 consequently gives the effective future
procedure. This proves $1\Rightarrow2,3$ without assuming that each
new row stores its old marker.

For the converse, suppose $G(P)$ fails. Choose $aL,q\in P$ with
$a\npreceq q$. The words $a,q$ are incomparable: if $q\preceq a$, then
$q$ would be a distinct prefix of $aL$, contradicting prefix-freeness.
Let $T=\{p\in P:a\npreceq p\}$. Every member of $T$ is incomparable
with $a$, and $q\in T$. Construct the finite trie whose distinguished
leaves are $a$ and the words in $T$; at each required internal node
supply both children, filling any unused child by a concrete alpha leaf.
Put a concrete beta at $a$ and one hole at each $p\in T$.
All public cuts under $a$ are blocked by its beta leaf; every cut outside
that cone is a reached hole. The result is one $P$-admissible exterior.

Give its holes singleton classes. Fill $q$ by alpha in one source and
beta in the other; fill the remaining holes in both sources by distinct
branch trees. These values are distinct from both leaves and from each
other, so (NAR.1.4) realizes the same old row in both sources.
There is a left birth at $aL$, whose value is beta.
The transported $q$ value is beta in the first source and a branch in
the second. Their next partitions differ. This excludes any next-row
factor, effective or otherwise, and any common future procedure.
Thus $2\Rightarrow1$ and $3\Rightarrow1$; the next row is also an
evaluation of the future procedure at one.

A zero-query service from a complete row-only handoff has identical
accessible initial state on the two sources, so its deterministic
calculation must give the same output. Authentication and the permitted
update supply no distinguishing label; its outputs cannot be correct
on both constructed sources. Conversely the explicit finite
calculation above supplies the zero-query value service when $G(P)$
holds, with actual entry and update permissions separately supplied.
The output is a row value, not a declaration of a new acquisition event.
$\square$

**Theorem 6.3 (edge cuts and a supplied obstruction).** The empty cut, root cut,
every singleton cut, $\{L,R\}$ and every cut whose words all end in $R$
satisfy $G$. The cuts $\{LL,LR\}$ and $\{LL,R\}$ respectively satisfy
and fail it. For the latter cut, reuse the actual sources from
[Sparse History Proposition 65.3, (SLH.65.2)](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md):

$$
x=\langle\beta,\alpha\rangle,\qquad
y=\langle\beta,\beta\rangle.
\tag{NAR.6.2}
$$

They have the same old row
$(\langle\beta,\square_R\rangle,\{\{R\}\})$ and different next rows.

**Proof.** The empty and root cuts have no word ending in $L$.
For a singleton $\{aL\}$ its only member extends $a$; a singleton
ending in $R$ has no condition. In $\{L,R\}$ the only relevant parent
is $\varepsilon$. In $\{LL,LR\}$ every member extends $L$.
All-$R$ endings satisfy the condition vacuously.
For $\{LL,R\}$ take $a=L$ and $q=R$.

For the supplied pair (NAR.6.2), the next exterior is
$\langle\langle\square_{LL},\alpha\rangle,\square_R\rangle$.
The two hole values are beta and beta for $x$, but beta and
$\langle\beta,\alpha\rangle$ for $y$. The next partition therefore
has one class for $x$ and two classes for $y$, and the actual legal
query at $R$ on their updated sources returns beta versus branch.
The full producer traces need not agree; the complete handoff forgets
them. This is the existing obstruction, used here to illustrate the
complete geometry classification, not a second discovery of that pair.
$\square$

## 7. Exact fresh raw-call count on the first updated version

**Assumption 7.1 (complete row-only entry and stationary re-query).** Fix a
realized $R=(C,\pi)$. The initial compatible original sources are exactly
$\mathcal U_R$ of (NAR.1.4), and the alpha supplement has been discarded.
The accessible entry state is determined by $P,R$ and common controls
alone, in the complete access-cut sense of Definition 4.3.
There is no retained history, ancestry, source size, pointer, timing,
source label or meter which restricts this full fiber.
Under the separately supplied serial entry and version contract, one
actual update has produced the authenticated register $y=\rho u$ for
some $u\in\mathcal U_R$. The register remains stationary throughout
the subsequent reading phase.

A comparison service is one common deterministic rule which, using
only its retained inputs and chronological native four-reply reads,
terminates on every such source and outputs the entire $R_P(y)$.
It may choose any finite addresses, adapt, repeat and compute locally.
The price is the number of fresh native raw invocations in this phase,
including re-reads. It is not a count of lifetime distinct addresses.
The authenticating promise states continuity and the one update,
without telling the service which source in the fiber is actual.

**Theorem 7.2 (sharp first-version worst-case calls).** Under Assumption 7.1,
the minimum deterministic worst-case fresh raw-call count is

$$
q(R)=
\begin{cases}
0,&L_C=\varnothing,\\
k,&L_C\ne\varnothing.
\end{cases}
\tag{NAR.7.1}
$$

This includes $k=0$. A protocol attaining it also obtains sufficient
finite data to calculate every later same-$P$ row algebraically.

**Proof.** With no left birth, use Theorem 2.1 and make no source read.
Otherwise query the current root at one retained address $p_b$ for
each old class, in canonical order, until a beta reply is obtained
or all classes are tested. The old-hole transport supplier and
(NAR.2.3) give

$$
r_{\rho u}(p_b)=
\begin{cases}
\beta,&z_b=\alpha,\\
\mathsf{branch},&z_b\ne\alpha.
\end{cases}
\tag{NAR.7.2}
$$

These roots exist and are images, so alpha and absence cannot occur.
A beta reply identifies the sole old alpha class; all $k$ negative
replies identify $\bot$. Apply Theorem 2.1 to obtain the entire next
row. Right births also determine its alpha label, so the next
conditional augmented record is known and Theorem 3.1 applies.
This uses at most $k$ calls and terminates sourcewise. If $k=0$ there
are no tests.

For the matching lower bound assume $L_C\ne\varnothing$ and $k>0$.
Choose mutually distinct non-alpha old class values, for example the
$c_j$ in Theorem 5.2, and let $u_0$ be their legal filling.
Run any correct deterministic comparison service on $\rho u_0$.
If it stops after fewer than $k$ calls, at least one old class $b$
has no query at any address extending any occurrence $p\in b$.
Indeed old-hole cones are disjoint, so a query enters at most one
old class cone; queries outside all cones enter none.

Replace the value of this class, at all its occurrences, by alpha to
obtain a second original source $u_1$. The other values remain distinct
and non-alpha, so $u_1\in\mathcal U_R$. After substitution the two
registers can differ only inside the old cones belonging to $b$.
At their proper ancestors the constructors are still branches; at
every other queried address the whole navigation and reply is
unchanged. Therefore induction along the deterministic run gives
the same queries, replies, local choices, stopping point and output
on $\rho u_1$. This comparison uses two alternative inputs; it
performs no unlisted destructive edit during either run.

The old alpha labels are $\bot$ and $b$. A left birth collides with
class $b$ only for $u_1$, so Theorem 2.1 gives different required next
partitions. The common output is wrong on one source, a contradiction.
Every correct service must consequently use at least $k$ calls on
the chosen no-alpha source. The upper bound attains this worst case.
For $k=0$, or with no left birth, the zero bound is already sharp.
$\square$

**Definition 7.3 (distinct resource coordinates).** The native
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean)
`paid` is the set of distinct addresses in a chronological history.
It charges a repeated address once within that history. Theorem 7.2
instead counts actual new invocations after the handoff and update.
The full producer has already queried every old representative root.
Thus under a separately declared lifetime address-only union price,
the representative-root protocol adds zero previously unseen addresses,
despite making up to $k$ new calls on a new version. Epoch-address
pricing or an empty ledger for the new phase is a different coordinate.
An old-version reply is not a current raw-cache hit.

The supplemental bit count in Theorem 5.2 excludes the concrete exterior,
complete class table, addresses, public cut and program, acquired data,
workspace, outputs and any event archive. Raw-call counts exclude
acquisition, addressing and address transmission, local computation,
memory, entry, authentication and actual updates. These costs remain
separate as in
[Sparse History Proposition 62.4](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).
The full-fiber call optimum is an immediate one-update, stationary
deterministic optimum; it is not an optimum for arbitrary extra history,
later image-restricted epochs, randomized expectation or other resources.

## 8. Substantive nonrecovery and attribution

**Theorem 8.1 (current conditional augmentation need not recover its predecessor).**
There is no function on realized current $S_P$ records which recovers
their predecessor $S_P$, even when the current source is known to be one
native substitution image. In particular it need not recover the
predecessor row.

**Proof.** Set $P=\{L,R\}$, $u=\beta$ and
$v=\langle\alpha,\beta\rangle$. The old row of $u$ is the concrete beta
tree with no holes, whereas that of $v$ has two unequal holes.
In the first old row both births occur and the alpha label is $\bot$;
in the second there is no concrete beta exterior leaf and the supplement
is $*$. Thus their old augmented records differ.

But $\rho u=\langle\beta,\alpha\rangle$ and
$\rho v=\langle\beta,\langle\beta,\alpha\rangle\rangle$ both have
the same current exterior $\langle\square_L,\square_R\rangle$ and
two unequal classes. This exterior has no concrete beta leaf, so
both current conditional supplements are $*$. Hence

$$
S_P(\rho u)=S_P(\rho v),\qquad R_P(u)\ne R_P(v).
\tag{NAR.8.1}
$$

The actual sources remain distinct by supplied injectivity; projection
to the conditional row has forgotten the distinction. The ordered
two-row recovery in Theorem 3.3 retains the current first row as an
input and does not assert inversion from its successor alone. $\square$

**Theorem 8.2 (fixed-cut closure preserves neither arbitrary queries nor changed cuts).**
Even in a left-birth geometry, two sources can have identical conditional
augmentations and identical same-$P$ rows at every epoch, but different
native raw replies and different rows for another cut at the next epoch.

**Proof.** Take $P=\{LL,R\}$ and

$$
s=\langle\beta,\beta\rangle,\qquad
t=\langle\beta,\langle\alpha,\alpha\rangle\rangle.
\tag{NAR.8.2}
$$

Both old rows are $(\langle\beta,\square_R\rangle,\{\{R\}\})$.
In both, the sole old class is not alpha, so the needed label is $\bot$.
Theorem 3.1 gives all their same-$P$ future rows equal. However,

$$
r_{\rho s}(RR)=\alpha,\qquad r_{\rho t}(RR)=\beta.
\tag{NAR.8.3}
$$

Indeed their right subtrees after one step are respectively
$\langle\beta,\alpha\rangle$ and $\langle\beta,\beta\rangle$.
For $Q=\{RL,RR\}$, the current exteriors are both

$$
\left\langle\langle\beta,\alpha\rangle,
                  \langle\square_{RL},\square_{RR}\rangle\right\rangle,
\tag{NAR.8.4}
$$

but the $Q$ holes are unequal for $s$ and equal for $t$.
This is an actual native source pair with different changed-cut rows,
not an arbitrary assignment to unrelated observations.
Even the universally safe root cut has only one constant row for
every source and epoch, while the actual root replies on $\rho\alpha$
and $\rho\beta$ are beta and branch. Fixed-cut recovery is therefore
strictly relative to its requested row family. $\square$

The scope distinction agrees with
[Sparse History §§64--65 and §§74--75](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md):
their original-source recutting task is $R_Q(u)$, not automatic
maintenance of the evolving $R_P(\rho u)$.
[NativeSymbolicRecutting](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean),
`symbolic_recut_exact`, supplies fieldwise symbolic recutting under
its explicit depth and filling hypotheses; it is not a missing-marker
acquisition theorem. The locality result
[NativeAlphaSpineObservation](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation.lean),
`native_alpha_spine_observation`, and the existence result
[NativeFiveHoleJointChoice](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFiveHoleJointChoice.lean),
`joint_finite_choice`, retain their own scopes.
The acquisition supplier
[ActualPureAcquisitionCompiler](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualPureAcquisitionCompiler.lean)
likewise does not turn semantic filling existence into free retention
or a supplemental-bit optimum.

**Mathematical citation 8.3 (suppliers and literature).** Node birth, address and
subtree transport, injectivity and image parsing are the §22 suppliers
cited in Theorem 2.1. Complete acquired rows, their legal source fibers,
joint history filtering, finite feasibility and actual handoff are the
§§59--62 suppliers cited in §§1,4,5; the same-row obstruction is the
published Proposition 65.3 cited in Theorem 6.3. General invariant-core
and finite-fiber distinction principles are reused, not proposed as
new abstract results. The repo-derived ordinary content here is the
complete collision table, its conditional alpha recurrence and
finite-epoch/two-row recovery, the specialized geometry equivalence,
and the conditional supplemental and first-version call equalities.

The relevant mature auxiliary-view context is
[Liang--Li--Wang--Orlowska, “Making multiple views self-maintainable in a
data warehouse”, *Data & Knowledge Engineering* 30 (1999), 121--134](https://doi.org/10.1016/S0169-023X(99)00009-9),
§2.1 and Theorem 2
([author text](https://users.cecs.anu.edu.au/~Weifa.Liang/papers/DKE99_30.pdf)).
Its self-maintenance input includes the modification content $dR$;
its minimality concerns removable auxiliary views and restrictions
on retained tuples. It supplies literature-attested context for
retaining auxiliary information. Direct transfer to this source would
require a faithful tree/update representation without extra
source-revealing notifications, and would still not identify conditional
state cardinality with that paper's minimality criterion.
Theorems 2.1--7.2 are justified directly on the native algebra and port.

For equality and disequality of finite subtrees, the literature-attested
background is
[Barguñó--Creus--Godoy--Jacquemard--Vacher, “Decidable Classes of Tree
Automata Mixing Local and Global Constraints Modulo Flat Theories”,
arXiv:1302.6960v2](https://arxiv.org/abs/1302.6960v2),
Definition 3.2, Theorem 5.22 and Corollaries 5.23--5.24.
The ranked signature $\{\alpha:0,\beta:0,\mathrm{mul}:2\}$ with empty
equational theory fits its tree setting. An exact history-language
encoding is necessary for applying an emptiness theorem; the particular
joint feasibility supplier is already cited in §5.
Emptiness decidability supplies neither actual source values, a new
query port, the alpha recurrence nor the fresh-call optimum.
No generic automaton construction or worldwide originality conclusion
is needed for the native proofs.

## 追加锚（本行以下为增补区）

## 9. Joint conditional supplement and first-version invocation frontier

**Assumption 9.1 (acquired supplement and complete updated entry).** Fix a
finite public prefix-free cut $P$, a realized complete old row $R=(C,\pi)$,
its canonically ordered class set $B$ with $k=|B|$, and the full unrestricted
original-source fiber $\mathcal U_R$ of (NAR.1.4). Before losing access to
old values, the producer has the truthful same-source, same-version finite
data of Assumption 4.1. A supplement $\sigma(u)$ is computed from these
actually acquired data and is actually exported together with $R$ before
the complete access cut. Semantic existence of a legal filling, or a
semantic inverse of a source name, does not supply these premises.

The reader's entire accessible initial state is a function of
$P,R,\sigma(u)$ and common source-independent controls, and these inputs
are recoverable from it. There is no additional source-dependent initial
field: old trees, representative values, archives, pointers, source
identity, readable control, acquisition order, lengths, meters and timing
are not extra inputs. A length or other field determined by the retained
payload does not add a distinction; any further accessible distinction
would change this assumption and its source fibers.

A separately supplied legal entry preserves the same source register,
and exactly one actual authenticated legal $\rho$ update gives
$y=\rho u$. The register is stationary during reading, and every reply
is the native four-reply value $r_y(a)$ at its requested finite address.
Continuity and authentication certify that register and version, without
revealing which $u\in\mathcal U_R$ is actual. No source-revealing update
packet is supplied. An already stopped producer is not resumed by this
assumption; the new entry and update are separate supplied conditions.
These are the supplement-bearing form of Definition 4.3 and Assumption
7.1, with the acquired full-row and serial boundary supplied by
[Sparse Literal History Transport, §§59--62](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).

**Definition 9.2 (two conditional prices and joint feasibility).** A
supplement may depend on all acquired finite class values, not only on
$A_P(u)$. Its conditional state count is

$$
m_R(\sigma)=|\sigma[\mathcal U_R]|.
\tag{NAR.9.1}
$$

One common deterministic reader receives the inputs of Assumption 9.1.
It may compute locally and choose arbitrary finite native addresses
adaptively from those inputs and its chronological replies. It must
terminate on every $u\in\mathcal U_R$ and output the entire
$R_P(\rho u)$. Let $Q(u)$ count its fresh native invocations during this
stationary first-updated-version phase. Every invocation counts, including
repeated addresses, absent-address calls, and re-reads of addresses
queried during old acquisition.

For integers $r\ge1$ and $q\ge0$, write $\mathsf{Feas}_R(r,q)$ if there
exist such an acquired and exported supplement and such a reader with
$m_R(\sigma)\le r$ and $Q(u)\le q$ for every $u\in\mathcal U_R$.
Write $\mathsf Q_R(r)$ for the least feasible integer $q$, when it exists.
This optimizes the existence of the encoder and reader jointly; it does
not assert that every supplement using at most $r$ values admits the same
call bound.

The first coordinate counts extra retained values conditional on the
already supplied row. It is not total controller states, workspace,
row size, program bytes or physical memory. The second coordinate counts
fresh invocations, not lifetime distinct addresses or physical time.
Acquisition, export and retention, the old row, local computation,
addresses and their transmission, authentication, actual updates and
later execution lie outside these two coordinates. They remain separate
requirements and costs, as in Definition 7.3 and
[Sparse History Proposition 62.4](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).

**Proposition 9.3 (updated native witnesses and all-address correspondence).**
Put $H=B\cup\{\bot\}$. There is a family
$(u_i)_{i\in H}\subseteq\mathcal U_R$ with $A_P(u_i)=i$ such that every
finite native address on $(\rho u_i)_{i\in H}$ has a constant reply or a
reply differing from one common value at at most one index $b\in B$.
If $L_C\ne\varnothing$, the required entire next rows
$(R_P(\rho u_i))_{i\in H}$ are pairwise distinct. These statements include
$k=0$, when the family has one member.

**Proof.** Use the mutually distinct non-alpha trees from Theorem 5.2,
$c_0=\beta$ and $c_{j+1}=\langle\beta,c_j\rangle$. Choose from this
sequence a distinct tree $t_b$ for each canonically named $b\in B$.
Define class tuples by

$$
z_c^{\bot}=t_c,\qquad
z_c^b=
\begin{cases}
\alpha,&c=b,\\
t_c,&c\ne b,
\end{cases}
\qquad
u_i=C[(z_{[p]}^i)_{p\in O}].
\tag{NAR.9.2}
$$

Every tuple has distinct values on distinct classes, since the assigned trees are
distinct and none is alpha. All occurrences of the same class use the
same value. Thus (NAR.1.4), supplied by
[NativeCutFibers](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean),
`legal_values_row` and `rowFiberEquiv`, makes these actual original sources
with exactly the same complete row, including its disequalities and
absent-cut guards. Their alpha labels are exactly their indices. For
$k=0$ the empty filling gives $u_{\bot}=C$.

Fix any finite address $a$. If no old hole address is a prefix of $a$,
the native descent never enters a replaced value. Substitution changes
only the fixed concrete part along that descent, so its reply is the
same for all $i$. In particular, every strict ancestor of an old hole
remains a branch, while a descent blocked in the transported concrete
exterior is blocked identically for every candidate. This is the
hole-exterior case of
[Sparse History Definition 60.1 and Theorem 60.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md).

Otherwise prefix-freeness gives a unique $p\in O$ and suffix $w$ with
$a=pw$. Put $b=[p]$. The actual old-hole transport and the defining
native descent give

$$
r_{\rho u_i}(pw)=r_{\rho z_b^i}(w)=
\begin{cases}
r_{\beta}(w),&i=b,\\
r_{\rho t_b}(w),&i\ne b.
\end{cases}
\tag{NAR.9.3}
$$

This uses the actual
[native four-reply `readout`](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean),
not an extra comparison port. There is no depth or existence restriction
on $w$: the first value is beta for the empty suffix and absent for every
nonempty suffix; the other value is whatever the fixed tree $\rho t_b$
really returns. If the two values agree the query is constant, and if
they differ it separates only candidate $b$. Multiple occurrences of
$b$ obey the same equation, but one address enters only one old hole
cone. Thus repeated occurrences, repeated queries, deep and absent
addresses, and strict ancestors give no missing case.

When a left birth $\ell\in L_C$ exists, Theorem 2.1 says that in the next
partition it is equal to old representative $p_b$ exactly on source
$u_b$. On $u_{\bot}$ it is unequal to every old class. Hence the complete
next partitions, and therefore next rows, are distinct for all indices.
Equivalently this is Theorem 3.1's exact conditional distinction.
For the one-member family the distinction is vacuous. $\square$

**Theorem 9.4 (attained joint conditional frontier).** Under Assumption 9.1,
for every integer $r\ge1$ and $q\ge0$, if $L_C\ne\varnothing$ then

$$
\mathsf{Feas}_R(r,q)
\quad\Longleftrightarrow\quad
r(q+1)\ge k+1,
\qquad
\mathsf Q_R(r)=\left\lceil\frac{k+1}{r}\right\rceil-1.
\tag{NAR.9.4}
$$

If $L_C=\varnothing$, a constant supplement and zero fresh invocations
suffice, so $\mathsf{Feas}_R(r,q)$ holds for all these $r,q$ and
$\mathsf Q_R(r)=0$. The nonempty-left-birth formula concerns the full
original fiber and the first updated version, with arbitrary
full-value-dependent supplements and arbitrary adaptive native queries.

**Proof, necessity.** Suppose $L_C\ne\varnothing$ and restrict any feasible
supplement and reader to Proposition 9.3's actual witness family. For
each used supplement value $s$, put

$$
H_s=\{i\in H:\sigma(u_i)=s\}.
\tag{NAR.9.5}
$$

The nonempty $H_s$ partition $H$ into at most $r$ parts, regardless of
how the supplement depends on the full old values. Within one such part,
the entire initial state is common. Authentication and the update do
not add a source distinction. Pairwise distinct required rows mean that
the reader must distinguish every index in $H_s$.

For a query entering class $b$, encode its reply on the witnesses by a
bit which is true exactly when it differs from the common default
$r_{\rho t_b}(w)$ in (NAR.9.3). If both displayed replies agree, use
constant false. For a query outside all old cones also use constant
false. At the selected address the bit reconstructs the entire native
reply: the address fixes the default and the possible exceptional value.
Thus no four-reply information is lost on this family. Every resulting
question is constant or true on at most the single index $b$, including
after restriction to $H_s$.

The correspondence applies at every adaptive history: the reader's next
address is determined by the common state and earlier replies, which
are reconstructed from the earlier bits. Once a run has stopped, pad
its mathematical transcript to length $q$ with constant false questions;
these padding symbols are not native invocations. At a bit history not
realized by any candidate, set all further questions constant false.
Such a history is detected by simulation on the finite witness set and
cannot be a prefix of an actual candidate's transcript. This gives the
all-histories question condition, not merely a condition on one run.

The length-$q$ bit transcripts are injective on $H_s$. Indeed, if two
candidates had the same transcript, deterministic reconstruction would
give the same native addresses, replies, stopping decision and returned
row. Early stopping does not lose information in padding: the stopping
decision is itself determined by the common preceding history, so a
second candidate with that prefix stops there too. Equal outputs would
contradict Proposition 9.3.

Apply the existing adaptive capacity bound
[SingletonQueryCapacity](../../../D5/S3/ConceptDynamics/Coding/SingletonQueryCapacity.lean),
`singleton_or_constant_query_capacity`, with finite source type $H_s$
and depth $q$. Its singleton-or-constant, all-histories and injectivity
hypotheses have just been supplied by the actual updated native queries
and whole-row target. It gives $|H_s|\le q+1$. Summing over the nonempty
parts yields

$$
k+1=\sum_{s:H_s\ne\varnothing}|H_s|
\le |\{s:H_s\ne\varnothing\}|(q+1)
\le r(q+1).
\tag{NAR.9.6}
$$

The witnesses are alternative fixed sources, each with its own actual
acquisition and export. The argument neither edits a register during
reading nor assumes that their discarded acquisition records agree.

**Proof, attainment.** Let $N=k+1$ and $d=\min\{r,N\}$. In the public
canonical order of $H$, with $\bot$ placed last, partition $H$ into $d$
nonempty blocks $G_1,\ldots,G_d$ whose sizes differ by at most one.
Their largest size is

$$
\max_j|G_j|=\left\lceil\frac{N}{d}\right\rceil
=\left\lceil\frac{N}{r}\right\rceil.
\tag{NAR.9.7}
$$

The finite block table depends only on the old row and $r$. From the
actually acquired data, Theorem 4.2 extracts the actual alpha label
$A_P(u)$ without additional acquisition queries. Export as $\sigma(u)$
only its block index $j$. All labels are realized on $\mathcal U_R$ by
Theorem 5.2, so this supplement uses exactly $d\le r$ actual values.
The block table is common; the actual block index is the entire extra
source-dependent initial input.

On receiving $j$, choose an omitted label $t_j$: choose $\bot$ if it
belongs to $G_j$, and otherwise the least class in $G_j$. Query one old
representative root $p_b$ for each $b\in G_j\setminus\{t_j\}$, in
canonical order, stopping at the first beta reply. Every queried label
is an old class, since a block containing $\bot$ omits it. The actual
updated-root replies are exactly (NAR.7.2): beta means $A_P(u)=b$, and
branch means $A_P(u)\ne b$. Alpha and absence do not occur at these
persisting roots. If all tests give branch, the only remaining label
in $G_j$ is $t_j$, which is therefore the actual label. In a singleton
block there are no tests.

This identifies the label on every source in the full fiber, not only
on the witnesses. Using that label with $P,R$, Theorem 2.1 constructs
the whole next exterior and complete partition. The reader therefore
returns the entire required next row with at most

$$
|G_j|-1\le\left\lceil\frac{k+1}{r}\right\rceil-1
\tag{NAR.9.8}
$$

fresh invocations. A source whose label is the omitted member of a
largest block realizes all those negative tests, so this reader's
worst-case count is exactly the right-hand side. Such a source exists
by Theorem 5.2. For integer $q\ge0$, the inequality $r(q+1)\ge k+1$ is
equivalent to $q\ge\lceil(k+1)/r\rceil-1$. Necessity and attainment
give (NAR.9.4).

If there is no left birth, Theorem 2.1 already computes the next row
from $P,R$ alone; export one common supplement and make zero calls.
If $k=0$, $H=\{\bot\}$ and the formula also gives zero for every
$r\ge1$, even when a left birth exists. With a left birth and $r=1$,
the formula is $k$, the endpoint of Theorem 7.2. With $q=0$ it requires
exactly $r\ge k+1$, the endpoint of Theorem 5.2; every $r\ge k+1$
admits singleton blocks and zero calls. These are the supplied endpoints
and their degenerate cases, not additional endpoint discoveries. $\square$

**Mathematical citation 9.5 (intermediate coverage and application boundary).**
The equality-search memory/call arithmetic and balanced encoder argument
are already supplied, on a different static comb family and geometric
target, by
[Word Retention and Geometric Reaccess, Theorem 4.2 and Corollary 4.3](RECURSIVE_RELATIONAL_OBSERVATION_WORD_RETENTION_AND_GEOMETRIC_REACCESS.md).
Their use here has $N=k+1$ candidate labels and $r$ supplement values;
their $2^b$-value case is the corresponding finite-state capacity case.
The generic adaptive singleton capacity is the cited existing
`singleton_or_constant_query_capacity`. Neither counting principle is
proposed as a new theorem here. The source-specific ordinary derivation
is Proposition 9.3's legal full-row-fiber family, its exhaustive
updated-native-address correspondence and next-whole-row distinction,
combined with Theorem 9.4's acquired/exported encoder and attainment on
the entire unrestricted fiber; this derivation is `repo-derived`.

The native algebra, collision recurrence, extraction and endpoint
suppliers remain Definitions 1.1--1.4 and Theorems 2.1, 3.1, 4.2, 5.2
and 7.2. The retained-view literature context belongs to Mathematical
citation 8.3; the classical decision-tree and equality-search context
belongs to the citations adjoining the cited geometric-reaccess results.
Those mature methods are intermediate coverage. This native application
does not assert worldwide novelty or a new generic advice/query law.

For a fixed arbitrary full-value-dependent supplement, its own fibers
can differ from the balanced alpha-label blocks; (NAR.9.4) is an
existential optimum, not a per-encoder performance guarantee. Additional
retained history can shrink $\mathcal U_R$ and exclude the witness family,
as Theorem 5.3 already demonstrates. No sharp lower law for such a
restricted fiber follows without a separate proof. The theorem likewise
does not transfer its sharp law to later image-restricted versions,
randomized readers, changed cuts or other resource coordinates. Its
output is a row value; neither a raw acquisition event nor a later actual
execution is furnished by that value.

## 追加锚（本行以下为增补区）

## 10. Exact relative native time across two acquired cuts

**Assumption 10.1 (the entire row-pair input).** Use the actual finite sources,
substitution, addresses and complete literal rows of Definitions 1.1--1.2.
The public cuts $P,Q$ are arbitrary finite prefix-free sets, each allowing
$\varnothing$ and $\{\varepsilon\}$. The entire source-dependent input is

$$
A=R_P(t),\qquad B=R_Q(\rho^k t),\qquad t\in\mathcal T,\quad k\ge0.
\tag{NAR.10.1}
$$

Both rows were truthfully acquired on their respective stationary versions.
Genuine same-source, same-root, pure-$\rho$ continuity between the captures
is supplied, without a numeric epoch or update count. The unknown first
version $t$ need not be primitive or a designated origin. No hidden hole
value, cross-row subtree-identity relation, origin calibration, source
identity label, producer log or earlier archive is supplied. Each row's
partition compares its own reached holes only.

The complete accessible handoff is determined by $P,Q,A,B$ and these common
conditions. As in Definition 4.3 and
[Sparse History, Assumptions 59.3 and 62.1](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md),
any accessible source-dependent pointer, control, size, allocation length,
query count, timing, cache or archive would be an additional input and
would change the fiber. Continuity certifies a relationship within an
actual history; it supplies no distinguishing name of its unknown source.

Acquisition remains a paid premise. The actual full-source producer in
[Sparse History, Definition 59.2](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md)
and [NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean),
`native_source_producer`, terminates on every finite stationary source,
reads each actual node once, and compares already acquired finite subtrees
locally. Its full trace and acquired tree contain more information than a
row. Exporting exactly the row, and supplying an actual lawful later
handoff, are separate conditions; that producer does not automatically
perform this export or continue after absorbing stop. No free row,
unknown-value equality oracle or update action is inferred.

Write $a\preceq b$ for prefix, including equality, and put

$$
\begin{aligned}
\operatorname{Gap}(P,Q)
 &=\{q:\ \forall a\in P\cup Q,\ a\npreceq q\ \text{and}\ q\npreceq a\},\\
D&=\max\bigl(\{0\}\cup\{|a|:a\in P\cup Q\}\bigr).
\end{aligned}
\tag{NAR.10.2}
$$

The union need not be prefix-free. A universal decoder for these cuts is
one effective rule returning $k$ from the declared input for every finite
$t$ and every $k\ge0$, without a source-size or first-epoch restriction.

**Theorem 10.2 (exact all-epoch cross-cut criterion).** Under Assumption 10.1,
a universal decoder exists if and only if $\operatorname{Gap}(P,Q)$ is
nonempty, equivalently $P\cup Q$ leaves an infinite binary ray uncovered.
The sufficient rule is uniform in the public cuts. If the union covers
every ray, no single-valued rule, even without an effectiveness requirement,
works universally. More precisely, in that case there are finite sources
$X,Y$ such that for every $n,h\ge0$,

$$
\begin{aligned}
R_P(\rho^nY)&=R_P(\rho^nX),\\
R_Q(\rho^{n+h}Y)&=R_Q(\rho^{n+h+1}X).
\end{aligned}
\tag{NAR.10.3}
$$

These are equalities of entire literal rows, including all brackets,
labels, reached guards and the complete equality/disequality partitions.

**Proof.** The finite prefix geometry is the supplier in
[Acquired Relation History, Definition 5.1](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md).
A depth-$D$ word without a prefix in $P\cup Q$ is incomparable with every
union member, since all their lengths are at most $D$. Every extension of
such a word is an uncovered ray. Conversely an uncovered ray has such a
depth-$D$ prefix. A gap word of any length also gives uncovered rays:
a union member on an extending ray would be comparable with that word.
Thus finite enumeration at depth $D$ decides the condition and selects a
common gap word when one exists. Equivalently one may first remove union
members with a shorter union prefix and test the resulting finite frontier.
A Kraft sum on the unreduced, possibly nested union is not this test.

For the all-epoch sufficient direction, reuse the intrinsic depth

$$
\nu(u)=\max\{j\ge0:u\in\rho^j[\mathcal T]\},\qquad
\nu(\rho u)=\nu(u)+1,\qquad \nu(\alpha)=0,\quad\nu(\beta)=1.
\tag{NAR.10.4}
$$

These are the supplied laws of
[IntrinsicSubstitutionCoordinates](../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean),
`intrinsic_coordinates` and `all_source_coordinate_law`.
[Acquired Intrinsic Depth Calibration, Reuse 2.2](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md)
supplies effective finite-tree inverse parsing, with termination; it does
not require a raw inverse operation on the source.

For any finite address $q$, let $a(u,q)$ be its longest actually reached
prefix in $u$. The root always exists. With $w(a)=\#_L(a)+2\#_R(a)$, the
absence-safe local expression is

$$
J_q(u)=w(a(u,q))+\nu\bigl(u|_{a(u,q)}\bigr).
\tag{NAR.10.5}
$$

If $q$ is absent, the subtree in this expression is the concrete blocking
leaf, never a subtree at an absent address. The equivalent recursion is

$$
\begin{aligned}
J_\varepsilon(u)&=\nu(u),\\
J_q(\alpha)&=0,\quad J_q(\beta)=1 &&(q\ne\varepsilon),\\
J_{Lr}(\langle x,y\rangle)&=1+J_r(x),\\
J_{Rr}(\langle x,y\rangle)&=2+J_r(y).
\end{aligned}
\tag{NAR.10.6}
$$

It verifies the expression's exact law at every epoch. For the empty
address use (NAR.10.4). At a nonempty address, $\alpha\mapsto\beta$ changes
zero to one. For $\beta\mapsto\langle\beta,\alpha\rangle$, a left first
edge gives $1+J_r(\beta)=2$ and a right first edge gives
$2+J_r(\alpha)=2$, including $r=\varepsilon$. Both advance the old value
one by one. For an originally paired tree, induction on the remaining
address and homomorphism give the same increment. Iterating yields

$$
J_q(\rho^k u)=J_q(u)+k\qquad(q\text{ arbitrary},\ u\in\mathcal T,\ k\ge0).
\tag{NAR.10.7}
$$

When $q$ is incomparable with every member of $P$, its navigation cannot
meet a hole in $C_P(u)$. If it stops early, its blocking leaf is literal.
If it reaches $q$, there is no cut below $q$, so the entire subtree there
is concrete in that exterior. Hence the reached prefix and the required
finite subtree in (NAR.10.5) are both available from the literal exterior.
Finite parsing gives an effective factor $j_{P,q}$ with

$$
j_{P,q}(R_P(u))=J_q(u).
\tag{NAR.10.8}
$$

No partition comparison, hidden value or fresh source query is used.
This verifies both the absence-safe proposal and its actual-row
factorization. In particular $q=L,u=\beta$ gives $J_q(u)=1=w(q)$ although
$L$ is absent. A numeric clock value is not an address-existence test;
the literal guard remains separate.

Choose the same $q\in\operatorname{Gap}(P,Q)$ at both captures. Then

$$
\mathsf{decode}(P,Q,A,B)=j_{Q,q}(B)-j_{P,q}(A)=k.
\tag{NAR.10.9}
$$

Subtraction here is integer subtraction, nonnegative on the promised
inputs. The decoder terminates on finite rows by the supplied parser.
There is no late-entry or saturation assumption: the preceding argument
includes early absent addresses, arbitrary first versions and $k=0$.

For necessity suppose the union covers every ray. Let $S_D=\{L,R\}^D$,
ordered lexicographically with indices $i(s)=0,\ldots,2^D-1$. Let $\mathcal
B_D$ be the perfect ordered depth-$D$ binary skeleton with leaf slots $s$;
$\mathcal B_0$ is a single slot. Put

$$
\begin{aligned}
T_j&=\rho^j\alpha,\qquad M=2D+2,\qquad H_s=M i(s),\\
\chi(s)&=\mathbf1_{\{\exists p\in P:\ p\preceq s\}},\\
X&=\mathcal B_D[(T_{H_s})_{s\in S_D}],\\
Y&=\mathcal B_D[(T_{H_s+\chi(s)})_{s\in S_D}].
\end{aligned}
\tag{NAR.10.10}
$$

All indices are nonnegative and all fillings are actual finite native
trees. This constructs two fixed original sources, independently of
$n,h$. Homomorphism gives their entire trajectories by adding the epoch
to every leaf index. Every $P$ or $Q$ address is reached in all these
versions because it lies at depth at most $D$ in the skeleton.

Outside $P$, a leaf slot has $\chi(s)=0$, so its fillings in $\rho^nX$
and $\rho^nY$ agree exactly. Every changed slot is strictly inside or
at a $P$ hole. The whole first exteriors therefore agree. Outside $Q$,
union coverage forces $\chi(s)=1$. At such a slot the fillings in
$\rho^{n+h}Y$ and $\rho^{n+h+1}X$ are both $T_{H_s+n+h+1}$.
All remaining differences lie inside $Q$ holes. The whole second
exteriors agree too. This establishes every exterior bracket and label,
not just their depths or a selected visible value. All reached sets are
the full corresponding cuts, so their absence guards agree as well.

It remains to verify every partition bit; exterior agreement alone would
not suffice. Reuse the existing right clock

$$
c(\alpha)=0,\qquad c(\beta)=1,\qquad
c(\langle x,y\rangle)=2+c(y),\qquad c(T_j)=j.
\tag{NAR.10.11}
$$

Its iterate law is `right_clock_iterate` in
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean),
and [Transport--Memory Completion, (RA.2307)](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md).
For a cut address $a$, write $s_a=aR^{D-|a|}$ for its rightmost skeleton
leaf. In the versions at any epoch $m\ge0$ the actual hole clocks are

$$
\begin{aligned}
c((\rho^mX)|_a)&=H_{s_a}+2(D-|a|)+m,\\
c((\rho^mY)|_a)&=H_{s_a}+2(D-|a|)+\chi(s_a)+m.
\end{aligned}
\tag{NAR.10.12}
$$

Different addresses in one prefix-free cut have different $s_a$:
an equality of these leaves would make the addresses comparable.
Their $H$ values differ by at least $M$, whereas the remaining offsets
before the common $m$ lie between zero and $2D+1$. Thus their clocks
differ by at least $M-(2D+1)=1$. Equal native trees have equal right
clocks, so all hole values in each row are pairwise unequal. This proves
that each of the two first $P$ partitions and each of the two second
$Q$ partitions is the same discrete partition. It includes each
reflexive equality and every off-diagonal disequality. Class names are
fixed by hole order, independent of the hidden values. Definition 1.2,
or the supplied `canonicalRow_record_iff`, now gives exactly (NAR.10.3).

The alternatives are the genuine histories $(\rho^jY)_{j\ge0}$ and
$(\rho^jX)_{j\ge0}$, each on its own fixed source and root. Capture both
first rows at $n$, and capture their second rows after $h$ and $h+1$
updates respectively. No endpoints have been spliced, no mid-history
edit or rerooting is performed, and no inverse action is needed.
Unknown originals may differ across these alternative realizations;
requiring an identified common original across alternatives would add
information excluded by Assumption 10.1. Truthful producers can acquire
all displayed rows; their discarded traces need not agree.

The complete decoder input is identical in these alternatives but the
required answers differ. Taking $h=0$ proves zero-versus-one ambiguity;
any $h\ge1$ proves strictly positive-lag ambiguity, at any first epoch
$n$. This excludes every universal decoder and completes both directions.
The witness family suffices to refute a rule quantified over all sources;
it imposes no size or fully-reached-entry restriction on that quantified
task. $\square$

**Proposition 10.3 (edge cuts, compatibility and authenticity).** Empty, root,
nested and disjoint cuts retain the full criterion of Theorem 10.2. Its
negative direction concerns universal decodability, not ambiguity of
every particular row pair. Define the endpoint lag fiber by

$$
\Lambda_{P,Q}(A,B)=\{k\ge0:\exists t\in\mathcal T,
                 \ R_P(t)=A,\ R_Q(\rho^k t)=B\}.
\tag{NAR.10.13}
$$

For a gap pair this fiber has at most one element, computable from any
chosen common $J_q$ whenever the fiber is inhabited. Nonnegative coordinate
consistency alone does not establish inhabitation. Neither inhabitation
nor a coordinate calculation authenticates a selected physical history.

**Proof.** For $P=Q=\varnothing$ the common address is $\varepsilon$;
the rows are full finite trees and their intrinsic-depth difference gives
the lag. If either cut contains the root, its prefix freedom makes it the
root singleton and the union covers; Theorem 10.2 applies, including $D=0$.
For disjoint incomplete cuts $P=\{L\},Q=\{R\}$ the union covers, whereas
$P=\{LL\},Q=\{RR\}$ leaves $LR$ uncovered. Nested union members cause no
exception: $P=\{L\},Q=\{LL,LR\}$ leaves $R$ uncovered, even though its
unreduced Kraft sum is one; $P=\{L\},Q=\{LL,R\}$ covers every ray.
These statements follow directly by inspecting the finite cylinders.

For a covering union take $P=Q=\{L,R\}$ and $A=B=R_P(\alpha)$.
The first row forces $t=\alpha$. Its later versions are beta at one and
branched at every epoch at least two, so this particular lag fiber is
$\{0\}$. Likewise $(R_P(\alpha),R_P(\beta))$ has the singleton lag fiber
$\{1\}$. Thus the universal obstruction does not assert instancewise
ambiguity. These examples retain their early absent-cut guards.

For a gap pair any member of (NAR.10.13) must equal (NAR.10.9), proving the
at-most-one assertion. For a consistency counterexample take both cuts
empty, $A=\alpha$ and $B=\langle\alpha,\alpha\rangle$ as full rows.
Both intrinsic depths are zero, so the proposed lag zero is nonnegative,
but the distinct trees are not related by that lag; no other lag can
belong to the fiber. Hence the fiber is empty. Endpoint satisfiability
is an existential mathematical condition. A real selected execution
still needs the acquisition and continuity premises of Assumption 10.1.
The coordinate is not their certificate. $\square$

**Proposition 10.4 (agreed-reference retention and its resource boundary).**
For public $P,Q$ and an agreed $q\in\operatorname{Gap}(P,Q)$, the single
integer $z=j_{P,q}(A)$ suffices as a summary of the first row for elapsed
count recovery after the second complete row is actually acquired.
For any $N\ge1$, every deterministic summary of that first row sufficient
for this same consumer on all sources needs at least $N$ distinguishable
values, and thus at least $\lceil\log_2N\rceil$ fixed-width bits on a
suitable finite family. There is no uniformly finite summary alphabet
for all elapsed counts. This is a statement about a specified summary
consumer, not a global minimum over summaries or total costs.

**Proof.** Compute $j_{Q,q}(B)-z$. If successive observations use cuts all
incomparable with the agreed $q$, retaining the same reference value
recovers counts relative to that capture; replacing it by the newly
extracted value permits the next difference. Each newly used row must
still be acquired. The scalar law (NAR.10.7) is closed as an arithmetic
identity, without a complete-row update procedure.

For the lower bound reuse generic answer counting, as in Theorem 5.2 and
[CompletionStateCardinality](../../../D5/S3/ObserverMemory/Prediction/CompletionStateCardinality.lean),
`completion_state_cardinality_mono`. Use the actual alpha orbit $T_i$.
Take first rows $R_P(T_i)$ for $0\le i<N$ and the common second row
$R_Q(T_N)$. All are legitimate histories, with required lags $N-i$.
Two equal retained summaries with this identical second row would force
one output for two different lags. Thus all $N$ summaries are distinct.
A fixed-width $b$-bit representation has at most $2^b$ values, giving
the stated bound. This applies generic counting to the native consumer;
it is not a new abstract counting principle. Each sufficient integer
is finite on a finite input, but its representation width is unbounded.
There is no fixed-bit or infinite-precision-unit-cost conclusion.

The agreement on the reference matters. If $Q$ is chosen only after the
old row was discarded, a previously chosen scalar is not universally
sufficient merely because the eventual union has a gap. For an actual
counterexample take the first cut empty and choose $q=\varepsilon$.
The sources

$$
u=\langle\beta,\langle\alpha,\alpha\rangle\rangle,
\qquad v=\langle\alpha,\alpha\rangle
\tag{NAR.10.14}
$$

are both primitive, so their retained root intrinsic depths coincide
at zero. Later choose $Q=\{R\}$. The $Q$ row of $u$ and the $Q$ row of
$\rho v=\langle\beta,\beta\rangle$ are both
$(\langle\beta,\square_R\rangle,\{\{R\}\})$, but their lags are zero
and one. The full first rows could have used the common gap $L$;
the discarded first rows cannot be replaced by their root scalar for
that task. One must agree on a reference that remains visible, or retain
the old row until the next common reference can be selected. Pairwise
gaps among successive cut pairs do not ensure a reference common to
an entire sequence: the successive singleton cuts $\{L\},\{RL\},\{R\}$
have gap $RR$ for the first pair and gap $L$ for the second, while all
three together cover every ray.

For a covering union, even retaining the entire first row cannot repair
the collision (NAR.10.3) under the declared input. For a gap union, scalar
retention asserts no complete-row closure. The existing sources of
Theorem 6.3 at $P=\{LL,R\}$ have a common visible gap but equal old
rows and different successor partitions. The distinct full-row criterion
remains Theorem 6.2.

Acquisition, full-row and class-table storage, public addresses and their
transmission, installed programs, local parsing and workspace, outputs,
source storage, permissions, authentication and readable old archives
are separate resources. Paying once to acquire a row does not pay for
another version's row or provide a cross-version cache hit. A genuine
continuation and each lawful entry remain supplied operations. No
$\mathsf{ApplyRho}$ service follows from the scalar difference. Relative
counts do not recover an uncalibrated absolute origin: beta can be the
initial beta source or the first image of alpha. Nor do they recover
physical elapsed time or a discarded execution archive. $\square$

**Mathematical citation 10.5 (owned suppliers and transfer conditions).** The
source algebra, complete rows and actual fibers are the suppliers of
Definitions 1.1--1.2. Fixed-cut alpha memory, the criterion $G(P)$,
predecessor nonrecovery and changed-cut nonrecovery remain the results
of §§2--8. Finite prefix geometry is owned by Acquired Relation History,
Definition 5.1; reached-subtree transport and saturation are owned by
[Native Signed Feasibility, Lemma 9.2 and Theorem 9.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md).
The exact right clock, intrinsic coordinates and finite parser are the
suppliers cited in the proof, not new coordinate discoveries.

[Native Birth Provenance, Theorem 4.2 and Proposition 7.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md)
already uses visible blocking leaves to compute absent-address
continuation and distinguishes intrinsic depth from elapsed epoch at
an uncalibrated origin. Its fixed-cut past-row recovery assumes a
supplied numeric epoch and retained birth information. Those inputs
are not present in (NAR.10.1). Its producer, handoff and resource
boundaries are consistent with Assumption 10.1 and remain separately
owned. The repo-derived content here is the exact cross-cut relation,
especially the single native construction preserving both full
partitions for every covering union. It is established here by ordinary
proof, without a worldwide originality claim.

The literature-attested prefix-code antecedent is
[Berstel--De Felice--Perrin--Reutenauer--Rindone, *Bifix codes and Sturmian
words*, arXiv:1011.5369v2, Proposition 3.3.1](https://arxiv.org/html/1011.5369v2).
Apply its prefix-comparability characterization with the factorial
language $\{L,R\}^*$ and, for a nested union, its prefix-minimal frontier.
That paper's codewords are nonempty; the root singleton is handled
directly here. Finiteness of the frontier yields the depth-$D$ ray test.
This supplies mature geometry, not native elapsed-count identifiability
or the simultaneous partition-preserving collision.

[Béal--Perrin--Restivo, *Recognizability of morphisms*, arXiv:2110.10267v3,
Theorem 1](https://arxiv.org/html/2110.10267v3) concerns unique centered
substitution representations of aperiodic points in an infinite
substitution subshift. The native leaf-word projection has the morphism
$\alpha\mapsto\beta$, $\beta\mapsto\beta\alpha$, but projection forgets
brackets and occurrences. Applying that theorem requires its infinite
subshift and aperiodicity conditions; it cannot replace the finite-tree
parser, the complete row-fiber argument, or authentication of an origin
or a history. The proofs above use the inspected native suppliers on
all finite ordered trees instead.

## 追加锚（本行以下为增补区）
