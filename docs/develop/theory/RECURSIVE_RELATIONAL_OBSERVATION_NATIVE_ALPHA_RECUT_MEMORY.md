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

## 11. Retaining a reference before the future cut is known

**Assumption 11.1 (encoding, discard and the later entire row).** Use all
actual finite ordered sources, the substitution and the complete rows of
Definitions 1.1--1.2. Fix public $D\ge0$ and a finite individually
prefix-free cut $P$ with $\operatorname{maxdepth}(P)\le D$, taking the maximum of an
empty set to be zero. The encoder receives exactly the truthfully acquired
$R_P(t)$, with $t$ any member of $\mathcal T$. It exports a finite code
$E_{P,D}(R_P(t))$ before the future cut $Q$ is known, and the first row is
then discarded. One decoder must satisfy

$$
\begin{aligned}
&\exists E_{P,D},\mathsf{Dec}_{P,D}\ \forall t\in\mathcal T
\forall Q\in\mathcal Q_D(P)\ \forall k\ge0,\\
&\mathsf{Dec}_{P,D}\bigl(Q,E_{P,D}(R_P(t)),R_Q(\rho^k t)\bigr)=k,\\
&\mathcal Q_D(P)=\{Q:Q\text{ finite and prefix-free},
 \operatorname{maxdepth}(Q)\le D,\ P\cup Q\text{ leaves a binary ray uncovered}\}.
\end{aligned}
\tag{NAR.11.1}
$$

The union itself need not be prefix-free. Both captures are stationary
and genuinely acquired. Actual export and isolation of the first code,
and genuine same-source, same-root, pure-$\rho$ continuation between
captures, are premises. The continuation supplies no value of $k$ and
no name of the unknown source. The decoder subsequently receives the
public $P,D,Q$, the code and the entire acquired later row, including its
literal exterior, absent-cut guards and complete within-row partition.
It receives no hidden subtree values or cross-row hidden equality.

Every source-bearing datum surviving the discard is part of the code:
source IDs, origin or epoch fields, clocks, logs, sizes, pointers,
readable allocation distinctions and carried archives cannot be supplied
for free. Source-independent installed controls and public constants may
be common. A code's own representation length is part of its
representation; an additional distinguishing length is additional code.
The acquisition and lawful handoff boundaries are those of Assumption
10.1. No row value, finite-tree calculation or continuity premise performs
an acquisition, resumes an absorbed Stop, or authorizes an update.

**Definition 11.2 (the exposed depth frontier and the clock variant).** Put

$$
\begin{aligned}
W_D&=\{L,R\}^D,\qquad W_0=\{\varepsilon\},\\
A_D(P)&=\{w\in W_D:\nexists p\in P\text{ with }p\preceq w\},
\qquad r=|A_D(P)|,\\
s(a)&=\#_L(a)+2\#_R(a).
\end{aligned}
\tag{NAR.11.2}
$$

For any address $w$ and finite tree $u$, let $a(u,w)$ be the longest
actually reached prefix of $w$. Reuse the right clock $c$ of (NAR.10.11),
and define the absence-safe variant

$$
J^c_w(u)=s(a(u,w))+c\bigl(u|_{a(u,w)}\bigr).
\tag{NAR.11.3}
$$

The superscript matters. Write $J^\nu$ for the expression called $J$ in
(NAR.10.5); its subtree coordinate is intrinsic inverse depth $\nu$.
Here the coordinate is $c$, not $\nu$. For example, at the root of
$p=\langle\alpha,\alpha\rangle$, $J^\nu_\varepsilon(p)=0$ and
$J^c_\varepsilon(p)=2$. The tree $p$ has no substitution predecessor,
by the image parser of Acquired Intrinsic Depth Calibration, Reuse 2.2.
The two expressions have the same advancement law, without being
numerically identified on arbitrary sources.

**Theorem 11.3 (finite-vector sufficiency on every finite source).** Under
Assumption 11.1, the finite vector

$$
Z_{P,D}(u)=\bigl(J^c_w(u)\bigr)_{w\in A_D(P)}
\tag{NAR.11.4}
$$

in public lexicographic order factors effectively through $R_P(u)$ and
is a sufficient code for every allowed later $Q$ and every $k\ge0$.
The claim includes sources where some or all frontier addresses are
initially absent; it requires no saturation, designated alpha origin
or source-size bound.

**Proof.** The supplier `right_clock_iterate` in
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean)
gives $c(\rho^k u)=c(u)+k$. The expression (NAR.11.3) has the recursion

$$
\begin{aligned}
J^c_\varepsilon(u)&=c(u),\\
J^c_w(\alpha)&=0,\quad J^c_w(\beta)=1 &&(w\ne\varepsilon),\\
J^c_{Lv}(\langle x,y\rangle)&=1+J^c_v(x),\\
J^c_{Rv}(\langle x,y\rangle)&=2+J^c_v(y).
\end{aligned}
\tag{NAR.11.5}
$$

For the empty address the supplied clock law gives a one-step increment.
At a nonempty address, alpha becoming beta changes zero to one. Beta
becoming $\langle\beta,\alpha\rangle$ changes one to two: the left case
is $1+J^c_v(\beta)=2$, and the right case is
$2+J^c_v(\alpha)=2$, also when $v=\varepsilon$. For an originally paired
tree, homomorphism and induction on the remaining address give the same
increment. Thus induction and then iteration prove

$$
J^c_w(\rho^k u)=J^c_w(u)+k
\qquad(u\in\mathcal T,\ w\text{ any finite word},\ k\ge0).
\tag{NAR.11.6}
$$

This is the structural argument for this variant, not a substitution of
$c$ for $\nu$ in a numerical equality between the variants.

For $w\in A_D(P)$, every $p\in P$ has length at most $D$ and is
incomparable with $w$. Indeed $p\preceq w$ is excluded by definition,
and $w\preceq p$ would, at these lengths, force $w=p$. Navigation toward
$w$ in the literal exterior $C_P(u)$ therefore never enters a hole. If
it stops early, it stops at a concrete alpha or beta leaf. If it reaches
$w$, the whole subtree there is concrete, since no $P$ cut is below $w$.
Let $a_C(w)$ be that navigation's final prefix. The actual exterior factor
is

$$
\gamma_{P,w}(C,\pi)
 =s(a_C(w))+c\bigl(C|_{a_C(w)}\bigr),\qquad
\gamma_{P,w}(R_P(u))=J^c_w(u).
\tag{NAR.11.7}
$$

In the early-stop case the subtree in this formula is the blocking leaf;
in the reached case it is the entire concrete finite subtree. The
navigation and the right-clock recursion terminate. The factor uses no
partition bit, hidden value or additional source Read. In particular an
absent $L$ at beta gives value one, while the reached $L$ at
$T_2=\langle\beta,\alpha\rangle$ gives value two. Reachedness comes from
the literal tree, not from treating a clock value as a presence test.

The finite geometry in Theorem 10.2 gives a depth-$D$ word $w$ with no
prefix in $P\cup Q$ whenever $Q\in\mathcal Q_D(P)$. Such a word belongs
to $A_D(P)$ and is incomparable with every $Q$ member too. Select the
least such word using only the public cuts. With $z_w$ its retained
coordinate and $B$ the acquired later row, define

$$
\mathsf{Dec}_{P,D}(Q,z,B)=\gamma_{Q,w}(B)-z_w.
\tag{NAR.11.8}
$$

Use integer subtraction; it is nonnegative and exactly $k$ on the
promised inputs by (NAR.11.6)--(NAR.11.7). Each finite tree gives finite
coordinates, so this is a finite effective code and decoder. Crucially,
the encoder computed every exposed coordinate before $Q$ was chosen;
only the decoder selects the common visible word. $\square$

**Definition 11.4 (actual separated-age sources).** Fix $H\ge0$ publicly,
put $b=H+1$, and enumerate all of $W_D$ as $w_0,\ldots,w_{m-1}$,
$m=2^D$. Let $\mathcal B_D$ be the full ordered depth-$D$ skeleton,
with $\mathcal B_0$ a single slot. Write $T_n=\rho^n\alpha$ and let
$I=\{j:w_j\in A_D(P)\}$. Choose independent ages $a_j\in\{0,\ldots,H\}$
for $j\in I$ and set $a_j=0$ for $j\notin I$. Define

$$
X_a=\mathcal B_D\bigl[(T_{jb+a_j})_{0\le j<m}\bigr],
\qquad Q_i=W_D\setminus\{w_i\}\quad(i\in I).
\tag{NAR.11.9}
$$

Every filling is an actual finite native tree. The offsets $jb$ and the
slots are public and independent of the age vector; the encoder receives
no age oracle. Let $\mathcal F_{P,D,H}$ be this finite source family.
The finite-family coding task is (NAR.11.1) with precisely this source
promise, still every $Q\in\mathcal Q_D(P)$ and every $k\ge0$.

**Theorem 11.5 (one fixed entire later row for each exposed index).** For
$i\in I$, $Q_i$ is an allowed future cut and there is one fixed entire
row $Y_i$, independent of every age in (NAR.11.9), such that

$$
R_{Q_i}(\rho^{H-a_i}X_a)=Y_i
\qquad\text{for every allowed age vector }a.
\tag{NAR.11.10}
$$

The initial $P$ rows of all these sources are distinct. The displayed
later equality includes every visible label and bracket, every reached
or absent guard, and every equality/disequality partition bit.

**Proof.** The cut $Q_i$ consists of distinct words of length $D$, hence
is prefix-free, including the empty cut when $D=0$. The ray through
$w_i$ has no prefix in $P$, and its only length-$D$ prefix is omitted
from $Q_i$. Thus $P\cup Q_i$ is noncovering.

Homomorphism leaves the full skeleton's brackets in place and sends its
slot $j$ at a common lag $k$ to $T_{jb+a_j+k}$. All depth-$D$ addresses
are reached, including at lag zero and when a filling is alpha. At
$k=H-a_i$, the only visible slot of the $Q_i$ exterior is exactly
$T_{ib+H}$. Every other slot is the address-marked hole at $w_j$.
Consequently the entire exterior is fixed, not merely one scalar
response. All $Q_i$ cut guards are reached; none is absent. The visible
slot is the same literal finite tree, so its internal labels, brackets
and absent-address replies agree as well.

To check the hidden partition, (NAR.10.11) gives $c(T_n)=n$, hence
$T_n=T_{n'}$ implies $n=n'$. At any common lag $k$, every slot index lies
in the interval

$$
[jb+k,jb+H+k].
\tag{NAR.11.11}
$$

For $j<j'$, the latter interval's minimum exceeds the former's maximum
by $(j'-j)b-H\ge1$. The actual slot trees are therefore pairwise
different after every common update, including slots whose ages were
fixed to zero under $P$. This proves all off-diagonal disequalities
between $Q_i$ holes and their reflexive equalities. Their partition is
always discrete, in public hole order. Different alternative histories
may use different common lags, but each has this same discrete partition.
Thus $Y_i$ is exactly the skeleton with slot $i$ filled by $T_{ib+H}$,
all other slots replaced by their holes, and that discrete partition.
For $D=0$ its partition is empty and $Y_0$ is the full tree $T_H$.
Definition 1.2 now proves (NAR.11.10) as an entire-row equality.

If two age vectors differ, choose a differing index $i\in I$. No $P$
cut contains or descends below $w_i$, so the initial exterior displays
the entire $T_{ib+a_i}$ there. Distinct indices give different displayed
trees by $c(T_n)=n$; therefore the initial $P$ rows differ. Every $P$
address is also reached in the skeleton. Its hidden subtrees consist
solely of slots under that cut, all with fixed age zero, so their whole
partition is constant across age vectors; it need not be discrete.
No lower-bound premise requires it to be discrete. The family comprises
$(H+1)^r$ sources and distinct initial rows. Each comparison uses its
own fixed original $X_a$ and its pure-$\rho$ trajectory; no history is
spliced and no mid-history source replacement is used. $\square$

**Theorem 11.6 (attained retained-value price and advance knowledge).** If
$r>0$, the least number of retained code values on
$\mathcal F_{P,D,H}$ sufficient for the finite-family task of Definition
11.4 is exactly

$$
(H+1)^r.
\tag{NAR.11.12}
$$

If a sole index $i\in I$ and its future cut $Q_i$ are public before
encoding, the corresponding least number is exactly $H+1$. The least
fixed-width binary widths are respectively

$$
\left\lceil r\log_2(H+1)\right\rceil
\quad\text{and}\quad
\left\lceil\log_2(H+1)\right\rceil.
\tag{NAR.11.13}
$$

**Proof.** Suppose two different age vectors received the same code in
the delayed-cut task. Choose a differing coordinate $i$. The decoder
would receive the same public $P,D,Q_i$, the same code and the same entire
$Y_i$ from Theorem 11.5, but the two required outputs $H-a_i$ differ.
No deterministic decoder can satisfy both. Every pair of vectors is
separated in this way, so the encoder is injective on the family's
$(H+1)^r$ distinct first rows. The code cannot access the chosen $i$ or
lag during encoding. This applies ordinary answer counting to the
actual entire-row witnesses, not to a scalar substitute for their input.

For attainment, the already sufficient code of Theorem 11.3 has, on
this family, the coordinates

$$
J^c_{w_i}(X_a)=s(w_i)+ib+a_i\qquad(i\in I).
\tag{NAR.11.14}
$$

All frontier slots are reached, so this follows from the definition and
$c(T_n)=n$. These coordinates take exactly $(H+1)^r$ different vector
values. Under the finite-family promise one can equivalently subtract
the public offsets, enumerate $I$ as $i_0,\ldots,i_{r-1}$, and encode

$$
M(a)=\sum_{h=0}^{r-1}a_{i_h}b^h,\qquad 0\le M(a)<b^r.
\tag{NAR.11.15}
$$

For $b\ge2$, successive Euclidean division by $b$ recovers the unique
$r$ digits, and every integer in this interval occurs. For $b=1$ all
ages are zero and the sole code is zero. Recovering the vector permits
(NAR.11.8) for every allowed $Q$, at every lag, not just the selected
lower-bound rows.

When $Q_i$ is known before encoding, only $a_i$ needs to be retained.
The initial exterior gives it by (NAR.11.14), and the later entire row
exposes the literal slot $i$ with clock $ib+a_i+k$. Subtract $ib+a_i$
to obtain $k$. This works at all $k\ge0$, regardless of other ages.
Conversely, vary $a_i$ through its $H+1$ choices with all other ages
fixed. At lags $H-a_i$, Theorem 11.5 gives the same complete $Y_i$ and
$H+1$ different outputs, forcing $H+1$ codes. Knowledge of the sole
index before encoding is the changed quantifier that permits this price.

A $B$-bit fixed-width code has at most $2^B$ values; conversely $N$
values fit in $\lceil\log_2 N\rceil$ bits by numbering them. Substituting
$N=b^r$ proves the first width in (NAR.11.13). It is a joint width,
not $r\lceil\log_2b\rceil$ separately rounded registers. For instance
$r=2,H=2$ needs nine values and four joint bits, while $r=3,H=2$
needs 27 values and five joint bits, rather than six. The $H=0$ case
has one value and zero bits. $\square$

**Proposition 11.7 (edge cases, positive lags and unbounded codes).** The
finite-vector theorem and the attained family include arbitrary $P$,
$D=0$ and $H=0$. If $r=0$, there is no legal future cut; the coding task
is vacuous and has a one-value, zero-bit code. If $r>0$, the all-source
task admits no fixed finite alphabet, even with strictly positive lags.
Nevertheless every actual vector can be encoded as one integer of
unbounded representation size.

**Proof.** A ray is uncovered by $P$ exactly when its depth-$D$ prefix
belongs to $A_D(P)$. Thus $r=0$ means $P$ covers every ray, and no union
with $P$ is noncovering. The family then has no independent ages and one
member; $(H+1)^0=1$ describes the vacuous minimum, with no available
index to which the known-index comparison could apply. If $r>0$, the
empty future cut is already allowed. At $D=0$, $P=\varnothing$ gives
$r=1$ and the only allowed $Q$ is empty; the family is
$\{T_a:0\le a\le H\}$ and its sharp price is $H+1$. The root first cut
instead gives $r=0$. At $H=0$ every family has one source, including
when several future indices are possible, and all the preceding proofs
retain this case.

To require strictly positive lags, replace (NAR.11.10) by

$$
R_{Q_i}(\rho^{H+1-a_i}X_a)=Y_i^+,
\tag{NAR.11.16}
$$

where the visible slot is $T_{ib+H+1}$. Its lag is at least one.
The same skeleton, reached guards and disjoint intervals give the same
fixed discrete partition. The two lags still differ whenever $a_i$
differs, so the exact lower counts and their attained upper codes are
unchanged. Here $H$ bounds the initial variable ages, not the permitted
lags of the decoder: the upper rules work for every lag.

For any proposed finite alphabet of size $N$ and fixed $r>0$, choose
$H$ so that $(H+1)^r>N$. That finite family is contained in the
all-source domain and violates the proposed alphabet by Theorem 11.6,
or by (NAR.11.16) under the positive-lag restriction. No bound on source
size was imposed on that domain. Each individual vector is still finite.
For example use the ordinary natural-number pairing

$$
\operatorname{pair}(x,y)=\frac{(x+y)(x+y+1)}2+y.
\tag{NAR.11.17}
$$

For fixed $x+y=n$ its values are the disjoint consecutive interval from
$n(n+1)/2$ to $n(n+1)/2+n$; these intervals partition the nonnegative
integers. This proves an effective unique inverse. Starting with zero,
pair successively with the $r$ coordinates and invert $r$ times; $r$ is
public. This encodes every vector as one natural number. Thus the number
of coordinates forces no register count. The integer's binary storage
size is unbounded and is not a unit-cost infinite-precision resource.

The finite-family optimum is a number of retained distinctions after
actual encoding and export. It is not a global all-source optimal bit
length, a uniform source-size bound, total acquisition memory or peak
workspace optimum. Full-row acquisition, installed program storage,
public-address representation, local calculation and comparison,
permissions and actual continuation keep their separate prices. Native
update count supplies no physical duration, space or energy law.
$\square$

**Proposition 11.8 (no coarsest sufficient equivalence in a full-tree
subtask).** In the all-source subtask $D=0$, $P=Q=\varnothing$, both
$E_\nu(u)=\nu(u)$ and $E_c(u)=c(u)$ are sufficient encoders for recovering
the unknown lag from the later whole tree. No sufficient equivalence
relation on first trees is coarser than both their kernel relations.
Consequently this subtask has no coarsest sufficient equivalence.

**Proof.** The whole initial tree is the acquired empty-cut row. The
intrinsic coordinate law (NAR.10.4), with its finite parser, makes
$\nu(v)-\nu(u)=k$ when $v=\rho^k u$. The right-clock supplier similarly
gives $c(v)-c(u)=k$. Both encoders are effective on every finite source
and retain just their respective integer.

For the actual trees $\alpha$, $p=\langle\alpha,\alpha\rangle$ and
$T_2=\langle\beta,\alpha\rangle$, the values are

$$
\begin{array}{c|ccc}
u&\alpha&p&T_2\\\hline
(\nu(u),c(u))&(0,0)&(0,2)&(2,2).
\end{array}
\tag{NAR.11.18}
$$

Alpha has no predecessor and $p$ is primitive by the supplied image
parser; $T_2=\rho^2\alpha$ has depth two by the intrinsic law. The right
clocks follow directly from their recurrence. Any equivalence coarser
than $\ker E_\nu$ merges $\alpha$ with $p$; any one coarser than
$\ker E_c$ merges $p$ with $T_2$. Transitivity then merges $\alpha$ and
$T_2$. But the identical later full tree $T_2$ requires lag two from
$\alpha$ and lag zero from $T_2$. With positive lags use the identical
later $T_3$, requiring three and one. A merged code fails on these
actual same-root pure-$\rho$ histories. This excludes even an
ineffective sufficient common coarsening. A coarsest sufficient
relation would have to be such a common coarsening, so none exists.

This obstruction is localized to this all-source lag task with later
whole-tree side information. It does not assert the same failure for
every $P,D$ or source restriction. The generic side-information
separation/coloring principle is already proved in
[Transport--Memory Completion, §8.2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md).
Conditional distinguishability need not be an equivalence whose
transitive closure remains sufficient. That observation does not
invalidate a task-specific stable behavioral quotient proved under its
own action, observation and target contract. $\square$

**Proposition 11.9 (the single-alpha-orbit contrast).** If the source
promise is instead only $t=T_n$ for an unknown $n\ge0$ and $r>0$, one
retained initial age $n$ suffices for every allowed $Q$.

**Proof.** Formula (NAR.11.6) gives, for every word $w$,

$$
J^c_w(T_n)=J^c_w(\alpha)+n.
\tag{NAR.11.19}
$$

Choose any public $w\in A_D(P)$ initially. The first exterior factor
recovers $n$ by subtracting the public $J^c_w(\alpha)$, which is zero.
After $Q$ is learned, select any common exposed depth-$D$ word $v$ as
in Theorem 11.3. Its later factor is $J^c_v(\alpha)+n+k$; subtract
the public initial-alpha constant and the retained $n$. This works
also before $v$ becomes reached. All the frontier coordinates on this
orbit equal $n$ and cannot vary independently. The separated-age
skeleton family belongs to the larger all-finite-source domain; its
$r$-age lower bound is not inferred from this one orbit. $\square$

**Mathematical citation 11.10 (suppliers, related coding and scope).** The
source and full-row suppliers are Definitions 1.1--1.2; the exact clock
and intrinsic parser are the suppliers used above. Sections 9 and 10
have different inputs: §9 conditions on a retained old row and acquired
hidden values for first-version whole-row recovery, while §10 retains
both acquired rows or agrees on a common reference before discarding
the first. Neither changes the encoder-before-$Q$ quantifier in
(NAR.11.1). The source-specific additions here are the delayed-cut
finite-vector factorization, the actual independent-age family with
fixed entire later rows and its attained price, and the native
no-common-coarsening counterexample. They are `repo-derived` ordinary
mathematical deductions, without a worldwide originality claim.

[NativeRankedNavigationCompiler](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler.lean),
`rank_only_refinement_compilation`, compiles records whose `Endpoint`
includes a supplied epoch and ranked expression; positive links use
both actual reached endpoints. It is not an acquisition of an unknown
lag or an extra cross-row equality input. Likewise
[NativePassiveServiceRealization](https://github.com/the-omega-institute/trureturing/blob/27141bb5e0ce1b5502224d5594c9a1bbe8525db1/D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.lean),
`bounded_passive_realization` and `materializeWholeRow`, realize bounded
passive runs at fixed epoch with installed common tables and paid
chronological replies. Their histories, epoch and installation inputs
are not free retained metadata in Assumption 11.1.

[Boundary Geometry Continuation IV, Theorems 113.4--113.5 and
113.7](https://github.com/the-omega-institute/trureturing/blob/27141bb5e0ce1b5502224d5594c9a1bbe8525db1/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md)
show that the original-tree boundary measure is invariant under $\rho$,
its fibers are actual primitive-orbit chains, and acquired scale restores
an injective source representation. That measure, denoted $\nu_u$ there,
is distinct from the intrinsic inverse depth $\nu(u)$ here. Those
source-bearing values are not additional inputs to Assumption 11.1;
whatever is determined by the actually acquired row may be computed
from it, including both values when the first cut is empty. The complete
INITIAL-row factorization in §113 keeps its different
retained-value and target contract. Its richer acquired representation
therefore does not furnish the delayed-cut code or its price for free.

The related literature is
[Charpenay--Le Treust--Roumy, *Optimal Zero-Error Coding for Computing
under Pairwise Shared Side Information*, arXiv:2211.03649v2,
Definition II.1, Definition IV.5 and Theorem IV.8](https://arxiv.org/html/2211.03649v2).
That paper studies asymptotic expected binary prefix-code length under
an i.i.d. source distribution. Its full-support formula uses the vector
of responses over compatible side-information values. This is useful
coding context, but no source probability, block limit or expected-rate
hypothesis is imposed here. The exact adversarial one-shot $b$-ary
count (NAR.11.12) follows from the native entire-row construction above,
not from that asymptotic rate theorem.

[Nayak, *Optimal lower bounds for quantum automata and random access
codes*, quant-ph/9904093v3, Theorem 2.3](https://arxiv.org/html/quant-ph/9904093v3)
bounds qubits for recovering individual binary bits with a prescribed
success probability. It is not by itself the present arbitrary-$b$
classical native count. No detailed Witsenhausen or Orlitsky theorem is
used as a premise; the needed finite separation argument is given
explicitly, with its generic principle already owned by §8.2 above.
The exact prices concern a specified attained finite family and retained
code consumer. They supply neither new kernel verification nor
acquisition or physical-resource optimality. Menus forced to expose
several slots remain outside the sharp known-index comparison proved
here.

## 追加锚（本行以下为增补区）

## 12. Exact native epochs from a family of acquired cut rows

**Assumption 12.1 (the entire multirecord input).** Use the finite ordered
native trees, homomorphic substitution and complete literal rows of
Definitions 1.1--1.2. Fix $m\ge1$ and public finite prefix-free cuts
$P_0,\ldots,P_{m-1}$, each permitting the empty and root cuts. The entire
source-dependent input is the ordered family

$$
\begin{aligned}
\mathbf R&=(R_{P_i}(\rho^{n_i}t))_{0\le i<m},\\
t&\in\mathcal T,\qquad 0=n_0\le n_1\le\cdots\le n_{m-1}.
\end{aligned}
\tag{NAR.12.1}
$$

Every row is truthfully acquired on its stationary version, in this
chronological order, along one genuine same-source, same-root, pure-$\rho$
history. The reference $n_0=0$ counts updates relative to the first
capture; $t$ is any finite source at that capture, with no designated
alpha origin. Continuity supplies no other numeric epoch, counter or
source name. Equal capture epochs are allowed.

The decoder receives exactly the public cuts, this ordered row family
and these common promises. Each row retains its entire literal exterior,
reached and absent-cut guards, and complete within-row equality/disequality
partition. Hidden subtree values, cross-row hidden-value links, source
IDs, origin calibration, logs, timing metadata, readable pointers,
distinguishing allocation or size fields, earlier archives and additional
source-bearing memory are absent. An accessible such datum would enlarge
the declared input. Acquisition, lawful handoffs and actual continuity
remain paid or supplied premises as in Assumptions 10.1 and 11.1.

For fixed cuts, a uniform effective decoder is one terminating rule on
this promise domain that gives the requested answer for every finite
$t$ and every chronological epoch vector in (NAR.12.1). This is an
all-source, all-epoch requirement, without a source-size, late-entry or
saturation restriction. It neither certifies an arbitrary row family's
compatibility nor authenticates an execution or a physical duration.

**Definition 12.2 (visible cells and the overlap graph).** Reuse the finite
frontier of Definition 11.2, putting

$$
\begin{aligned}
D&=\max\bigl(\{0\}\cup\{|p|:p\in P_i,\ 0\le i<m\}\bigr),\\
W_D&=\{L,R\}^D,\qquad W_0=\{\varepsilon\},\\
S_i&=A_D(P_i)=\{w\in W_D:\nexists p\in P_i\text{ with }p\preceq w\},\\
i\mathrel{\sim_G}j&\iff i\ne j\text{ and }S_i\cap S_j\ne\varnothing.
\end{aligned}
\tag{NAR.12.2}
$$

Let $\mathcal C$ be the connected components of this finite undirected
graph, $C(i)$ the component of capture $i$, $C_*=C(0)$ and
$h=|\mathcal C|$. A singleton graph is connected. Each component's
reference $r_C$ is its least capture index.

The finite prefix geometry of Theorem 10.2 identifies an edge exactly
with an uncovered binary ray for $P_i\cup P_j$. Indeed, an uncovered
ray's depth-$D$ prefix lies in $S_i\cap S_j$, and every extension of a
word in that intersection remains uncovered. Since all cut depths are
at most $D$, such a word is incomparable with every member of either
cut. The union need not be prefix-free. All cells, edges, components
and references can be found by finite enumeration of the public cuts.

**Theorem 12.3 (effective recovery within each component).** Under
Assumption 12.1, the entire vector

$$
\bigl(n_i-n_{r_{C(i)}}\bigr)_{0\le i<m}
\tag{NAR.12.3}
$$

is uniformly effectively recoverable. In particular a connected graph
permits recovery of $(n_i)_{0\le i<m}$. No single direction need be
visible in every capture.

**Proof.** Reuse the right-clock variant $J^c_w$ of Definition 11.2,
its exact all-source law (NAR.11.6) and actual-row factor (NAR.11.7).
They already include arbitrary finite addresses, reached or absent.
For each edge choose the lexicographically least
$w_{ij}=w_{ji}\in S_i\cap S_j$. For its orientation $i\to j$, compute
from the two acquired rows

$$
\begin{aligned}
d_{ij}
&=\gamma_{P_j,w_{ij}}(R_j)-\gamma_{P_i,w_{ij}}(R_i)\\
&=(J^c_{w_{ij}}(t)+n_j)-(J^c_{w_{ij}}(t)+n_i)
=n_j-n_i,\qquad d_{ji}=-d_{ij}.
\end{aligned}
\tag{NAR.12.4}
$$

Here $R_i$ denotes the corresponding member of $\mathbf R$. Navigation
in the exterior may stop at an early concrete blocking leaf. In that
case the supplied factor uses that leaf, never a hidden or absent
subtree. The right-clock recursion and navigation are finite; neither
the partition nor an additional source Read is needed for this factor.
Different edges may use different words.

Choose a spanning forest by finite traversal, rooted at each $r_C$.
Assign $z_{r_C}=0$ and, on each forest edge away from its root, assign
$z_j=z_i+d_{ij}$. Induction on the traversal gives
$z_i=n_i-n_{r_C}$. These are integer additions and subtractions: a path
can traverse an edge towards an earlier capture, even though capture
indices themselves are chronological. Every other path gives the same
answer, since the actual-history equalities in (NAR.12.4) telescope and
every closed-path sum is zero. If the graph is connected its reference
is $0$, with $n_0=0$. This is the usual integration of exact additive
offsets on a finite graph, applied to the supplied native row factors.
It supplies no new graph-integration mechanism. $\square$

**Lemma 12.4 (simultaneous component-owned whole-row collision).** For
any cuts in Definition 12.2 there is one attained whole-input fiber
containing $2^{h-1}$ distinct strictly chronological epoch vectors,
one for each independent bit on the components other than $C_*$.
All its alternatives are genuine native histories satisfying
Assumption 12.1. The corresponding complete row families coincide,
including every exterior, guard and partition bit.

**Proof.** Enumerate $W_D$ in lexicographic order as
$w_0,\ldots,w_{2^D-1}$. For each cell define its visibility set
$V_j=\{i:w_j\in S_i\}$. Any two distinct members of $V_j$ share that
cell and are adjacent. Thus a nonempty $V_j$ lies in one component.
Define its owner $o(j)$ to be that component, or $\bot$ if $V_j$ is
empty. This is one owner for the whole cell, simultaneously across all
captures, rather than a separate assignment for each row pair.

Let $\mathcal B_D$ be the full ordered depth-$D$ binary skeleton,
with $\mathcal B_0$ a single slot, and reuse $T_a=\rho^a\alpha$.
For independent bits $\delta_C\in\{0,1\}$ on $C\ne C_*$, put
$\delta_{C_*}=\delta_\bot=0$ and define

$$
\begin{aligned}
M&=2D+2,\qquad A_j=2+Mj,\\
t^\delta
&=\mathcal B_D\bigl[(T_{A_j-\delta_{o(j)}})_{0\le j<2^D}\bigr],\\
n_i^\delta&=2i+\delta_{C(i)}.
\end{aligned}
\tag{NAR.12.5}
$$

Every initial leaf age is at least one, so all fillings are actual
finite native trees. Also $n_0^\delta=0$ and
$n_{i+1}^\delta-n_i^\delta\ge2-1=1$. Each alternative therefore
uses one fixed source $t^\delta$ and its genuine forward trajectory,
with nonnegative strictly chronological captures. Choosing a different
positive original age is a construction of another original source,
not an inverse action, a replacement between captures or a rerooting.

Homomorphism of $\rho$ preserves the skeleton and advances each filling's
age. If capture $i$ sees cell $j$, its owner is $C(i)$, and its entire
actual subtree at that slot is

$$
T_{A_j-\delta_{o(j)}+n_i^\delta}=T_{A_j+2i},
\qquad w_j\in S_i.
\tag{NAR.12.6}
$$

It is independent of all the bits. Prune the skeleton at the addresses
in $P_i$. Every surviving depth-$D$ slot is precisely a member of $S_i$
and has the fixed filling (NAR.12.6); all intervening brackets and
address-marked holes are fixed too. Hence the entire concrete exterior
of row $i$ agrees in every alternative. No comparison of projected
scores substitutes for this literal equality. Every cut address has
depth at most $D$ and is reached in the full skeleton, in every version.
Thus each reached list is exactly $P_i$, and all absence guards agree.
For $D=0$ the same argument concerns the single root slot.

It remains to preserve the complete hidden partition. For a hole
$p\in P_i$, let $j(p)$ index its rightmost depth-$D$ descendant
$pR^{D-|p|}$. Reuse $c(T_a)=a$ and
$c(\langle x,y\rangle)=2+c(y)$ from (NAR.10.11). At any epoch $k\ge0$
the actual hidden subtree has clock

$$
c\bigl((\rho^k t^\delta)|_p\bigr)
=A_{j(p)}+2(D-|p|)-\delta_{o(j(p))}+k.
\tag{NAR.12.7}
$$

Distinct holes in one prefix-free cut have distinct $j(p)$: sharing a
descendant would make the two addresses comparable. The corresponding
$A$ values differ by at least $M$, whereas each remaining depth-and-bit
offset $2(D-|p|)-\delta_{o(j(p))}$ lies in $[-1,2D]$. Consequently,
for distinct $p,q\in P_i$, the absolute difference of their clocks is
at least $M-(2D+1)=1$, including when the holes have different depths.
Equal finite native subtrees have equal right clocks. Therefore every
row's distinct hidden holes have unequal values at every epoch, for
every bit choice. Each row has exactly the same discrete partition,
with every reflexive equality and every off-diagonal disequality.
Empty and singleton partitions require no separate spacing assumption.
Together with the exterior and guards, Definition 1.2 gives

$$
R_{P_i}(\rho^{n_i^\delta}t^\delta)
=R_{P_i}(\rho^{2i}t^0)
\qquad(0\le i<m).
\tag{NAR.12.8}
$$

The alternatives may have different originals, as the input contract
allows; each alternative itself has one unchanged original and root.
Each nonreference component contains a capture, necessarily indexed
above zero, whose epoch changes when that component's bit changes.
Thus the $2^{h-1}$ vectors are distinct. Some originals can coincide
when a component owns no visible cells; distinct originals are not
needed for distinct epoch vectors. All displayed rows can be truthfully
acquired from their respective finite stationary versions. $\square$

**Theorem 12.5 (sharp uniform recovery criterion).** For any fixed public
cuts in Assumption 12.1, the whole vector $(n_i)$ is uniformly effectively
recoverable if and only if $G$ is connected. For any fixed capture indices
$a,b$, the signed difference $n_b-n_a$ is uniformly effectively recoverable
if and only if $C(a)=C(b)$. In either negative case no single-valued rule,
even without an effectiveness requirement, works on every promised input.

**Proof.** Theorem 12.3 supplies both positive claims. For indices in the
same component, subtract their recovered coordinates in (NAR.12.3).

If $h>1$, Lemma 12.4 supplies an identical entire decoder input with
different required epoch vectors. Hence one rule cannot recover the
whole vector universally. If $C(a)\ne C(b)$, at least one of those
components is not $C_*$. Toggle just that component's bit, holding all
other bits fixed in the lemma. This changes $n_b-n_a$ by one or minus
one without changing the supplied rows. It excludes every universal
difference decoder. The collision is of whole row families, so any
higher-order inference from their exteriors, guards and within-row
partitions has identical input as well. It is not a necessity argument
inferred solely from linear edge equations. $\square$

**Proposition 12.6 (componentwise constraints do not classify every fiber).**
For arbitrary fixed rows define the chronological realization fiber

$$
\begin{aligned}
\mathcal E(\mathbf P,\mathbf R)
=\{\mathbf n\in\mathbb N^m:\ &0=n_0\le\cdots\le n_{m-1},\\
 &\exists t\in\mathcal T\ \forall i<m,\ R_{P_i}(\rho^{n_i}t)=R_i\}.
\end{aligned}
\tag{NAR.12.9}
$$

If this fiber contains $\mathbf n$ and $\mathbf n'$, then
$n'_i-n_i$ is constant on each component, and zero on $C_*$. This is a
necessary constraint, not a claim that every componentwise shift is
feasible. Disconnected cuts can have a singleton realization fiber.

**Proof.** Apply (NAR.12.4) to both realizations of the same rows. Every
edge gives $n'_j-n'_i=n_j-n_i$, so the differences are constant along
paths. At index zero both vectors vanish. The simultaneous feasible
bits in Lemma 12.4 belong to its deliberately constructed fiber; they
impose no affine-lattice classification on other fibers.

For a singleton disconnected instance take $m=2$, $P_0=\{L\}$ and
$P_1=\{R\}$, with both exteriors literally alpha, no reached holes and
empty partitions. Their union covers, so the graph has two components.
The first row forces $t=\alpha$. The second row forces
$\rho^{n_1}\alpha=\alpha$, hence $n_1=0$: $T_1=\beta$, and $T_k$ is
branched for every $k\ge2$. Thus this fiber is exactly $\{(0,0)\}$.
The all-source impossibility in Theorem 12.5 does not assert ambiguity
of every individual disconnected input.

Even coordinate consistency does not establish compatibility. With
both cuts empty, let the first full row be alpha and the second be
$\langle\alpha,\alpha\rangle$. Their root right-clock difference is
$2\ge0$, but the first row forces $t=\alpha$, and its epoch-two source
is $T_2=\langle\beta,\alpha\rangle$, not the second row. The factor law
excludes every other epoch, so the fiber is empty. Neither the forest
calculation nor fiber inhabitation authenticates a physical execution.
$\square$

**Proposition 12.7 (degenerate cuts and essential edge examples).** The
preceding claims include $m=1$, $D=0$, empty, root and ray-covering cuts,
early absence and equal epochs. A connected family need not have a ray
visible in every capture, and disconnected families admit concrete
strictly chronological whole-row collisions.

**Proof.** For $m=1$ the graph is connected and the required vector is
the known relative reference $(0)$, even for a root cut. Empty cuts
have $S_i=W_D$ and expose full trees; a root or any ray-covering cut
has $S_i=\varnothing$, hence is an isolated vertex. Such an isolated
vertex prevents whole-vector uniform recovery when $m>1$, regardless
of the particular row's reached guards. At $D=0$ every cut is empty
or the root singleton; the empty-cut vertices form a clique and each
root-cut vertex is isolated. This is exactly the same criterion.

No early absence is removed from the positive theorem. For example,
$P_0=\{L\}$ and $P_1=\{LL\}$ have a common visible depth-two cell
$RL$. At $t=\beta$ it is absent, with $J^c_{RL}(\beta)=1$. After one
update $T_2$ still blocks the full $RL$ address at its right alpha leaf,
with $J^c_{RL}(T_2)=2$. The exterior factors recover lag one while
retaining the literal reachedness information separately. Equal epochs
give zero on each applicable edge; strict chronology is a strengthening
of the negative witnesses, not a restriction of the decoder contract.

For a family needing different edge directions take

$$
\begin{aligned}
P_0&=\{RL,RR\},& S_0&=\{LL,LR\},\\
P_1&=\{LL,RR\},& S_1&=\{LR,RL\},\\
P_2&=\{LL,LR\},& S_2&=\{RL,RR\}.
\end{aligned}
\tag{NAR.12.10}
$$

The graph is the path $0$--$1$--$2$, with witnesses $LR$ and $RL$,
while $S_0\cap S_1\cap S_2=\varnothing$. The first and third cuts
alone have a covering union; the middle capture joins the two native
differences and permits whole-vector recovery. Reordering the cuts as
$P_0,P_2,P_1$ gives the path $0$--$2$--$1$. Its forest traversal uses
$d_{21}=n_1-n_2$, which can be negative on chronological inputs.

For a concrete disconnected collision put $P_0=\{R\}$,
$P_1=\{L\}$ and

$$
X=\langle T_2,T_6\rangle,\qquad Y=\langle T_2,T_5\rangle.
\tag{NAR.12.11}
$$

Capture $X$ at epochs $(0,2)$ and $Y$ at $(0,3)$. Both first rows have
exterior $\langle T_2,\square_R\rangle$; both second rows have exterior
$\langle\square_L,T_8\rangle$. Each row has its indicated reached
singleton hole and its singleton partition. These are equal whole
inputs with different positive lags on actual fixed-source histories.
The general lemma supplies the additional simultaneous mixed-depth
partition argument for arbitrary cut families. $\square$

**Proposition 12.8 (canonical boundary-density interpretation of the right
clock).** Reuse [Boundary Geometry Continuation IV, Definition 113.3 and
Theorems 113.4--113.5](https://github.com/the-omega-institute/trureturing/blob/30389d09d00d57c6887798af0c6aa3363c0240b8/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md).
Let $\varphi=(1+\sqrt5)/2$, $\Omega=\{L,R\}^{\mathbb N}$ and let the
Bernoulli probability satisfy $M([p])=\varphi^{-s(p)}$, with $s$ as in
Definition 11.2. For each finite $u$, write $W(u)=a(u)+\varphi b(u)$
for its alpha/beta leaf scale. On each original leaf cylinder $[p]$,
with label $\ell_p=0$ for alpha and $1$ for beta, use the canonical
locally constant representative

$$
f_u(\omega)=\frac{\varphi^{s(p)+\ell_p}}{W(u)}
\quad(\omega\in[p]),\qquad \nu_u=f_u M.
\tag{NAR.12.12}
$$

For every finite $u\in\mathcal T$ and every finite address $q$, reached
or absent, the exact identity is

$$
\varphi^{J^c_q(u)}=W(u)f_u(qR^\infty).
\tag{NAR.12.13}
$$

The locally constant representative is uniquely determined by the
attained measure value $\nu_u$. Arbitrary almost-everywhere representatives
and replacement of $J^c$ by $J^\nu$ do not satisfy this identity in general.
It gives a semantic interpretation, without supplying the decoder an
unacquired global measure, scale or point-evaluation oracle.

**Proof.** Every infinite ray in a finite tree reaches exactly one
original terminal leaf. Let $p$ be the terminal address on $qR^\infty$.
If $q$ is absent, $p$ is exactly its blocking leaf and
$J^c_q(u)=s(p)+\ell_p$. If $q$ is reached, then $p=qR^r$ for some
$r\ge0$. The right-clock recursion gives
$c(u|_q)=2r+\ell_p$, so again
$J^c_q(u)=s(q)+2r+\ell_p=s(p)+\ell_p$.
Substitution into (NAR.12.12) proves (NAR.12.13) in both cases, including
the root and terminal addresses.

Every finite cylinder has positive $M$ mass. If two locally constant
representatives of the same measure differed at one point, each would
be constant on a cylinder neighborhood of that point. On their common
smaller cylinder the two constants would differ, contradicting equality
almost everywhere. Thus the representative is unique; no unreduced
original-leaf description is extra information. A finite native tree's
leaf cylinders cover all of $\Omega$, so this proof uses the full source
domain, not merely eventually reached addresses.

The restriction on representatives is necessary. For $u=\alpha$ and
$q=\varepsilon$, the canonical $f_u$ is one, $W(u)=1$ and $J^c_q(u)=0$.
The singleton $\{R^\infty\}$ has zero mass, since
$M([R^r])=\varphi^{-2r}\to0$. Changing the density to two just at that
point gives the same Radon--Nikodym class and measure, but breaks the
identity. Point evaluation is justified by the canonical locally
constant representative, not by an arbitrary Radon--Nikodym derivative.

For $u=\langle\alpha,\alpha\rangle$ at the root,
$W(u)f_u(R^\infty)=\varphi^2$ and $J^c_\varepsilon(u)=2$.
In contrast, $J^\nu_\varepsilon(u)=\nu(u)=0$ by Definition 11.2 and
the supplied finite-tree image parser. Hence intrinsic inverse depth
cannot replace the right clock. The boundary measure $\nu_u$, scalar
intrinsic depth $\nu(u)$ and right clock $c(u)$ are distinct objects.

On a genuine history, the supplied scale action is
$W(\rho^n t)=\varphi^nW(t)$ and the boundary measure is invariant.
Uniqueness makes its canonical densities agree pointwise. For any one
edge word in (NAR.12.4), (NAR.12.13) therefore yields

$$
\frac{W(\rho^{n_j}t)f_{\rho^{n_j}t}(w_{ij}R^\infty)}
     {W(\rho^{n_i}t)f_{\rho^{n_i}t}(w_{ij}R^\infty)}
=\varphi^{n_j-n_i}.
\tag{NAR.12.14}
$$

All densities are positive. This interprets the already observable
integer difference; the decoder computes (NAR.12.4) from local acquired
exteriors. It does not acquire or consume either global factor in
(NAR.12.14). Identity (NAR.12.13) also holds semantically at covered
addresses, where the required value need not be observable from a row.
A density or clock value is not an address-presence test. $\square$

**Mathematical citation 12.9 (suppliers, content and acquisition boundaries).**
Definitions 1.1--1.2 and the cited `canonicalRow_record_iff`,
`legal_values_row` and `rowFiberEquiv` own the native algebra and complete
row semantics. Section 10 owns the two-cut theorem and separated-age
partition mechanism. Section 11, Theorem 11.3 and (NAR.11.6)--(NAR.11.7)
own the absence-safe all-source right-clock factors reused here;
$J^\nu$ has its separately supplied intrinsic-depth factor. Neither clock
is rediscovered or numerically identified with the other.

Exact-offset integration is mature. [Singer, *Angular synchronization
by eigenvectors and semidefinite programming*, arXiv:0905.3174v2,
§1](https://arxiv.org/html/0905.3174v2) explicitly gives spanning-tree
recovery on a connected graph and the undetermined offsets between
components. Its angular sums are modulo $2\pi$; its clock application
uses real offsets. The present native differences are exact integers.
The additive path formulation is already supplied by
[ZeroLoopPotentialEquivalence](../../../D5/S3/Observer/AgencyHolonomy/ZeroLoopPotentialEquivalence.lean),
`closed_path_zero_iff_exists_potential`, for an additive commutative
group on a connected groupoid, with composition additivity and inverse
antisymmetry. Here the path cost sums (NAR.12.4), $\mathbb Z$ supplies
the coefficient group, and actual-history telescoping supplies zero
loop costs on each connected component. Finite forest traversal makes
this application effective. This algebra does not itself prove that a
native whole-input collision realizes independent component offsets.

[NativeSymbolicRecutting](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSymbolicRecutting.lean),
`symbolic_recut_exact`, assumes every cut depth is strictly less than its
representation depth. It cannot be applied directly with that depth
equal to $D$ for the depth-$D$ holes here. Lemma 12.4 instead proves the
actual fields directly. [NativePositiveContextFiber](https://github.com/the-omega-institute/trureturing/blob/30389d09d00d57c6887798af0c6aa3363c0240b8/D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.lean),
`positive_context_history_exact` and `positiveContextEquiv`, supplies
positive repeated-role contexts with supplied epoch-zero constraints,
without different-role disequality. It does not supply this unknown-epoch
chronological family with complete partitions.
[NativeRankedNavigationCompiler](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler.lean)
retains each endpoint's supplied epoch, while
[NativePassiveServiceRealization](https://github.com/the-omega-institute/trureturing/blob/30389d09d00d57c6887798af0c6aa3363c0240b8/D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.lean),
`bounded_passive_realization`, carries its certified epoch and prior
chronological record. These are distinct input contracts, not decoders
for (NAR.12.1). [Reversible five-state FIB harmonic-edge-load optimization](https://github.com/the-omega-institute/trureturing/blob/30389d09d00d57c6887798af0c6aa3363c0240b8/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_REVERSIBLE_FIVE_STATE_SLICE_UNIFORM_SEPARATION.md)
has legal binary words and stationary laws as its objects; that task
supplies no multirecord native epoch theorem.

The substantive repo-derived content is the simultaneous component-owner
realization of Lemma 12.4, preserving genuine chronology and every full
row at once, and the resulting sharp uniform criterion. Proposition 12.8
is a dependent finite-density compatibility consequence of the existing
boundary profile and right clock. These statements have ordinary proofs
above; no worldwide originality or new kernel certification is asserted.

The consumer starts with all the declared rows acquired and retained.
Literal exteriors, partitions, public addresses and their transmission,
finite parsing, integer widths, workspace, source storage, permissions,
stationary entries, lawful handoffs and genuine continuity remain separate
resources or premises. No fixed-width optimum, full feasible-vector
solver, source reconstruction from rows, free full-profile acquisition,
future-row closure, update service, physical duration or execution
authentication follows from this relative-epoch theorem.

## 追加锚（本行以下为增补区）

## 13. Several visible positions and the memory retained before recutting

**Assumption 13.1 (one retained code and a k-position future menu).**
Use the actual finite ordered native trees, homomorphic $\rho$ and
complete literal rows of Definitions 1.1--1.2. Fix public $P,D,H$ as in
Definitions 11.2 and 11.4, with $H\ge0$ and $r=|A_D(P)|\ge1$. Keep the
original enumeration $W_D=(w_0,\ldots,w_{m-1})$, $m=2^D$, and put
$I=\{j:w_j\in A_D(P)\}$ and $b=H+1$. The source domain is exactly the
separated-age family of Definition 11.4:

$$
\begin{aligned}
X_a&=\mathcal B_D[(T_{jb+a_j})_{0\le j<m}],
&T_n&=\rho^n\alpha,\\
a&\in\{0,\ldots,H\}^{I},
&a_j&=0\quad(j\notin I).
\end{aligned}
\tag{NAR.13.1}
$$

In particular, offsets remain $jb$ at the original cell indices;
renumbering the exposed coordinates does not renumber these offsets.
Choose a public integer $1\le k\le r$. The future menu consists of
all $k$-subsets $S\subseteq I$, with associated cuts

$$
Q_S=W_D\setminus\{w_i:i\in S\}.
\tag{NAR.13.2}
$$

The encoder receives only the truthfully acquired initial $R_P(X_a)$,
exports one code before $S$ and the lag are known, and discards that
initial row. The decoder receives the code, public $P,D,H,k,S$ and
exactly the entire truthful later $R_{Q_S}(\rho^\ell X_a)$. Its target
is the unknown elapsed update count $\ell$. The required quantifiers are

$$
\exists E,\mathsf{Dec}\quad
\forall a\in\{0,\ldots,H\}^{I}\quad
\forall S\subseteq I, |S|=k\quad
\forall\ell\in L:\quad
\mathsf{Dec}(S,E(R_P(X_a)),R_{Q_S}(\rho^\ell X_a))=\ell,
\tag{NAR.13.3}
$$

where either $L=\mathbb N$ or $L=\mathbb N_{>0}$ is fixed publicly.
The letter $k$ counts visible positions, never the lag. Let
$N_H(r,k)$ be the smallest number of attained retained code values for
this task. Theorems below show it is the same for the two choices of $L$.
Its fixed-width binary representation price is
$\lceil\log_2 N_H(r,k)\rceil$.

Each capture is stationary and genuinely acquired, and the continuation
is genuinely same-source, same-root and pure-$\rho$. These are premises,
not information supplying $\ell$. All surviving source-bearing data
count as code, including IDs, numeric epochs, clocks, logs, sizes,
readable pointers or allocation distinctions and archives. The decoder
gets no hidden subtree values, cross-row hidden links or unacquired
whole-source profile. It does get every literal exterior label and
bracket, every reached or absent-cut guard and every within-row hidden
equality/disequality. Paid acquisition and lawful handoff are those of
Assumptions 10.1 and 11.1. This finite source restriction and restricted
future menu are essential; they do not replace the all-source or
all-allowed-cut contracts of §11.

**Definition 13.2 (the native menu conflict graph).** On the age vectors
in (NAR.13.1), define a finite undirected graph $G_{H,r,k}$ by

$$
a\mathrel{\sim_G}a'
\quad\Longleftrightarrow\quad
\exists d\in\mathbb Z\setminus\{0\}:\quad
|\{i\in I:a_i-a'_i=d\}|\ge k.
\tag{NAR.13.4}
$$

Exchanging the two vectors exchanges $d$ with $-d$, so the graph is
symmetric and has no loops. A code is proper when it gives different
values to adjacent vectors. Coordinates in graph calculations may be
identified with $1,\ldots,r$ by the public order of $I$; this leaves the
native offsets in (NAR.13.1) unchanged.

**Theorem 13.3 (whole-row collisions and exact retained-alphabet criterion).**
For every fixed $S$, all vectors $a,a'$ and all $\ell,\ell'\ge0$,

$$
\begin{aligned}
R_{Q_S}(\rho^\ell X_a)=R_{Q_S}(\rho^{\ell'}X_{a'})
&\quad\Longleftrightarrow\quad
 a_i+\ell=a'_i+\ell'\quad(i\in S).
\end{aligned}
\tag{NAR.13.5}
$$

There is a common entire later row at unequal allowed lags for some
menu choice exactly when (NAR.13.4) holds. An encoder in (NAR.13.3)
is sufficient exactly when its induced code on the age vectors is
proper. Consequently, with $\chi$ denoting ordinary finite chromatic
number,

$$
N_H(r,k)=\chi(G_{H,r,k}).
\tag{NAR.13.6}
$$

Every proper finite code has one effective finite decoder on the promised
inputs. None of these conclusions takes an equivalence closure of the
conflict relation or requires recovering the whole initial age vector.

**Proof, actual entire rows.** Every $Q_S$ is prefix-free. A ray through
any selected $w_i$ is uncovered by both $P$ and $Q_S$, so
$Q_S\in\mathcal Q_D(P)$. This includes $D=0$, $r=k=1$, where
$Q_S=\varnothing$. Homomorphism retains the full depth-$D$ skeleton and
puts $T_{jb+a_j+\ell}$ in its original slot $j$ at lag $\ell$.
The $Q_S$ exterior is therefore precisely that skeleton with these
literal trees at the selected slots and address-marked holes at every
other slot. All depth-$D$ slots are reached, even when a filling is
alpha. Every cut guard is reached; there are no absent cut members.
Inside a displayed tree, its labels, brackets and absent-address replies
are determined by that literal tree.

The clock supplier used in §11 gives $c(T_n)=n$. Hence $T_n=T_{n'}$
if and only if $n=n'$. In either history, the exponents at distinct slots
lie in the disjoint intervals

$$
[jb+\ell,jb+H+\ell],\qquad 0\le j<m.
\tag{NAR.13.7}
$$

Indeed, for $j<j'$ the gap between the intervals is at least
$(j'-j)b-H\ge1$. This includes slots outside $I$, whose ages are fixed
to zero. Thus every off-diagonal hidden comparison is false and every
reflexive one is true. The complete hidden partition is always discrete
in the public hole order, also for alternative histories with different
lags. A zero- or one-hole partition has the corresponding empty or
singleton form. There are no hidden-visible or cross-row comparisons
in the row contract.

Equality of entire rows therefore forces equality of every displayed
$T_{ib+a_i+\ell}$, giving the right side of (NAR.13.5). Conversely those
equalities fix the entire exterior, all its concrete labels and brackets,
every reached-cut guard and the same complete discrete hidden partition.
Definition 1.2, or its supplied `canonicalRow_record_iff`, then gives
whole-row equality. The graph reduction uses this complete-record proof;
a scalar alone would not have licensed the converse.

For unequal lags in (NAR.13.5), put $d=\ell'-\ell\ne0$. At least the
$k$ selected indices satisfy $a_i-a'_i=d$, proving a conflict edge.
Conversely, choose any $k$ indices having the same nonzero displacement
$d$ and take

$$
\ell=\max(1,1-d),\qquad \ell'=\ell+d.
\tag{NAR.13.8}
$$

Both lags are positive and distinct, and the selected translated ages
agree. Equation (NAR.13.5) gives the common whole row. Thus allowing zero
lags adds no edge to the positive-lag task. Each witness is one fixed
actual $X_a$ with its own pure-$\rho$ continuation; different histories
are compared, not spliced.

**Proof, the two coding directions and effectivity.** Initial $P$ rows
are distinct and display each exposed slot, by Theorem 11.5. The encoder
can compute its age from that acquired literal subtree alone:

$$
a_i=c(X_a|_{w_i})-ib
     =\gamma_{P,w_i}(R_P(X_a))-s(w_i)-ib.
\tag{NAR.13.9}
$$

Thus every code on the finite age domain is realizable from the actual
initial row without an age oracle. If a sufficient encoder gave the same
code to adjacent $a,a'$, (NAR.13.8) would present its decoder with the
same public $S$, the same code and the same entire later row, but different
required outputs. Necessity follows.

For sufficiency, parse the received later exterior at the selected slots
and subtract their public offsets to obtain

$$
z_i=c((\rho^\ell X_a)|_{w_i})-ib=a_i+\ell\qquad(i\in S).
\tag{NAR.13.10}
$$

Enumerate the finitely many vectors $u$ with the received code. Fix one
$i_0\in S$, set $h=z_{i_0}-u_{i_0}$ in $\mathbb Z$, and retain the
candidate if $h\in L$ and $z_i-u_i=h$ for all $i\in S$. This is a finite
procedure on acquired finite trees. One may also construct its finite
$R_{Q_S}(\rho^hX_u)$ and compare the complete literal record; on promised
inputs (NAR.13.5) makes this an equivalent test. The genuine source is
among the candidates. Two surviving candidates with different $h$ would
have a common nonzero displacement on $S$, contradicting properness.
All surviving candidates therefore have one and the same lag. Return
that lag. Several different initial vectors at the same lag are harmless.
Malformed or unpromised inputs may return failure.

This is the single-shot zero-error side-information bridge already proved
in [Transport--Memory Completion §8.2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#82-标签恰须切开可能混淆的前缀),
instantiated with the native entire-row collision just established.
Numbering the colors gives (NAR.13.6); the generic coloring principle is
not additional mathematical content here. Overlapping possible later
inputs are not the fibers of one deterministic source readout. For
example, when $H=1,r=3,k=2$, the pairs $000,110$ and $110,001$ are edges,
while $000,001$ is not. Replacing this graph by connected components
would introduce a false separation obligation. $\square$

**Theorem 13.4 (general finite-age bounds and matched endpoints).** For
$H\ge0$ and $1\le k\le r$,

$$
(H+1)^{\lfloor r/k\rfloor}
\ \le\ N_H(r,k)\ \le\ (H+1)^{r-k+1}.
\tag{NAR.13.11}
$$

In particular,

$$
N_0(r,k)=1,\qquad N_H(r,1)=(H+1)^r,\qquad N_H(r,r)=H+1.
\tag{NAR.13.12}
$$

If a single selected $k$-subset $S$ is known before encoding and is the
only future cut, its exact retained-value price is $H+1$, irrespective
of $k$. All these statements hold for either lag convention.

**Proof.** Put $q=\lfloor r/k\rfloor$. Partition $qk$ exposed indices
into $q$ disjoint $k$-blocks. Let each block have one freely chosen common
age in $\{0,\ldots,H\}$ and fix every leftover age to zero. There are
$b^q$ such actual sources. Any two choices differ on some entire block
by one nonzero displacement, hence are adjacent by Theorem 13.3.
This is a clique, so every proper code uses at least $b^q$ values.
The witnesses retain the original slot offsets and their complete native
row interpretation; they do not install a new subset-query port.

For the upper bound choose a fixed public set $F\subseteq I$ of size
$r-k+1$ and retain precisely $(a_i)_{i\in F}$, computed by (NAR.13.9).
Every $k$-subset $S$ intersects $F$, since $|I\setminus F|=k-1$.
Choose $i\in S\cap F$ from the public order and return $z_i-a_i$.
This uses $b^{r-k+1}$ attained values and works at every allowed lag.
Equivalently, vectors with the same retained coordinates cannot have a
nonzero displacement on an entire selected $S$. This construction proves
sufficiency, without asserting that the bound is generally sharp.

For $H=0$, the single vector gives $z_i=\ell$, so no distinguishing
memory is required. For $k=1$ the two bounds coincide at $b^r$; any pair
of different vectors has a differing coordinate and is an edge. For
$k=r$ they coincide at $b$; one retained acquired coordinate suffices.

For a known fixed $S$, retain the age at one public $i\in S$ and use the
same subtraction. For necessity let all selected ages have a common
value $v\in\{0,\ldots,H\}$, fixing the other ages to zero. The initial
rows are distinct. At the positive lags $H+1-v$, every selected normalized
age is $H+1$, so Theorem 13.3 gives one entire later row for these $b$
sources and $b$ distinct required lags. They require $b$ codes. This proves
the exact known-menu comparison, including $H=0$. $\square$

**Theorem 13.5 (sharp binary half-visibility boundary).** On precisely the
binary-age family $H=1$,

$$
\begin{aligned}
N_1(r,k)=2&\quad\Longleftrightarrow\quad 2k>r,\\
2k\le r&\quad\Longrightarrow\quad
 N_1(r,k)\ge 2^{\lfloor r/k\rfloor}\ge4,\\
r=2k&\quad\Longrightarrow\quad N_1(r,k)=4.
\end{aligned}
\tag{NAR.13.13}
$$

Thus the exact one-bit threshold is $k>r/2$. There is no parameter pair
in this binary domain whose optimal retained alphabet has three values.
At equality $r=2k$ the exact fixed-width price is two bits.

**Proof, a majority code and its actual decoder.** Write
$w(a)=\sum_{i\in I}a_i$. When $2k>r$, retain the bit

$$
E(a)=\begin{cases}1,&2w(a)>r,\\0,&2w(a)\le r.\end{cases}
\tag{NAR.13.14}
$$

This convention assigns any global tie to zero. Binary displacements
in a conflict edge can only be $1$ or $-1$. If $a_i-a'_i=1$ on at least
$k$ positions, then $w(a)\ge k>r/2$ and
$w(a')\le r-k<r/2$. The two codes differ; the reverse displacement is
symmetric. This proves properness.

There is also a direct decoder using (NAR.13.10). If the selected ages
are mixed, their normalized later values include both $\ell$ and
$\ell+1$, so return $\min_{i\in S}z_i$. The retained bit is unnecessary
on this input. If the $z_i$ are uniform, say all equal $t$, the selected
ages are either all zero with lag $t$, or all one with lag $t-1$.
Because $k>r/2$, their common selected age is the strict global majority:
all zero leaves at most $r-k<r/2$ ones, and all one provides at least
$k>r/2$ ones. Thus the retained bit is exactly that common age; return
$t-E(a)$. On promised inputs this has the correct allowed sign. The
same proof covers $k=1$ when it satisfies the threshold and $k=r$ when
the whole selected row may be mixed. No numeric epoch is retained.

The all-zero and all-one vectors are adjacent for every $k\le r$,
so a single code value is impossible. Both bit values are attained,
proving $N_1(r,k)=2$ above the threshold. At or below it the clique from
Theorem 13.4 has at least four members; this proves necessity, excludes
two- and three-value optima and supplies the stronger displayed block
lower bound.

**Proof, four attained colors at equality.** Let $r=2k$, choose one public
exposed index $i_*$ and assign four labels by

$$
C(a)=\begin{cases}
0,&w(a)<k,\\
1,&w(a)>k,\\
2+a_{i_*},&w(a)=k.
\end{cases}
\tag{NAR.13.15}
$$

Two vectors with weight below $k$ cannot have $k$ positive or $k$
negative binary differences: either direction would require one of them
to have at least $k$ ones. Two vectors with weight above $k$ cannot be
adjacent either: the smaller side in either directed edge would have at
least $k$ zeros and hence weight at most $k$. For two weight-$k$ vectors,
a conflict needs $k$ directed differences. Equal weights force $k$
reverse differences too; there are only $2k$ positions. The vectors are
therefore complementary and differ at $i_*$, so their labels differ.
Different weight categories already have disjoint labels. The code is
proper, and Theorem 13.3 supplies its effective decoder. All four labels
occur: all zero, all one, and weight-$k$ vectors with either value at
$i_*$. The two-disjoint-block clique has four members, giving the matched
lower bound. In particular, ties cannot be resolved by one arbitrary
majority bit at this boundary. $\square$

**Proposition 13.6 (native edge cases and the three-position contrast).**
The binary conclusions include $r=1,k=1$, all $k=r$ and all $k=1$.
Their exact alphabet sizes are respectively $2$, $2$ and $2^r$. A native
$r=3,k=2$ menu needs one bit, whereas the section 11 task on the same
binary source family needs three fixed-width bits when singleton
exposures remain allowed. This saving concerns the changed visibility
requirement, not an extra acquired source statistic.

**Proof.** The first two cases follow from Theorems 13.4--13.5. At $k=1$
every pair of distinct binary vectors is adjacent, so $2^r$ values are
both necessary and sufficient. For $r=2,k=1$ this is also the exact
half-boundary four-value case; for $r=2k$ at any $k$ Theorem 13.5 applies.

For a literal three-position realization take $D=2$, $P=\{RR\}$,
$I=\{0,1,2\}$ in the order $LL,LR,RL,RR$. The actual sources are

$$
X_a=\left\langle
       \langle T_{a_0},T_{2+a_1}\rangle,
       \langle T_{4+a_2},T_6\rangle
     \right\rangle,
\qquad a\in\{0,1\}^3.
\tag{NAR.13.16}
$$

The initial row displays the three variable trees and hides only $T_6$.
Each future $Q_S$ displays exactly two of those positions and hides the
other two depth-two slots. At any lag their hidden exponents are distinct,
so the whole hidden partition is discrete and all cut guards are reached.
Theorem 13.5's majority bit and its uniform/mixed decoder therefore apply
to these actual complete rows. Necessity follows already from the actual
$000,111$ pair: at lags $2,1$ the selected trees agree for every two-slot
choice, and the full rows agree by Theorem 13.3.

If the future menu instead allows each singleton $\{i\}$, Theorem 11.5
provides its fixed entire row at lags $1-a_i$, or $2-a_i$ for positive
lags. Every pair of distinct vectors differs at some exposed index, so
Theorem 11.6 forces all eight codes. The section 13 two-slot requirement
excludes exactly those singleton witnesses. It does not lower the price
under the broader section 11 menu. $\square$

**Proposition 13.7 (ternary multiset obstruction and a four-source clique).**
At $H=2,r=3,k=2$, a code depending only on the multiset of the initial
ages is insufficient. In particular the median, every fixed order
statistic, any tuple of quantiles and the entire sorted age list cannot
by themselves be a sufficient retained code. Independently,

$$
4\le N_2(3,2)\le9.
\tag{NAR.13.17}
$$

Neither assertion determines the exact ternary optimum.

**Proof, an entire-row positive-lag obstruction.** Keep $D=2$, $P=\{RR\}$
and $I=\{0,1,2\}$, but the original public offsets are now $0,3,6,9$.
Take $a=(0,1,2)$ and $a'=(1,2,0)$ and select $S=\{0,1\}$, so
$Q_S=\{RL,RR\}$. The actual original trees and lags are

$$
\begin{aligned}
X_a&=\langle\langle T_0,T_4\rangle,
                    \langle T_8,T_9\rangle\rangle,&\ell&=2,\\
X_{a'}&=\langle\langle T_1,T_5\rangle,
                    \langle T_6,T_9\rangle\rangle,&\ell'&=1.
\end{aligned}
\tag{NAR.13.18}
$$

Both later exteriors are exactly
$\langle\langle T_2,T_6\rangle,
\langle\square_{RL},\square_{RR}\rangle\rangle$.
The hidden trees in the first history are $T_{10},T_{11}$ and in the
second are $T_7,T_{10}$. In both, the two holes are reached and their
values unequal, so the complete partitions coincide, as do every
visible label, bracket and absent-address guard supplied by the literal
exterior. These are equal whole later rows with distinct strictly positive
lags. The two initial rows differ, but both age multisets are $\{0,1,2\}$.
Any permutation-invariant code therefore identifies them and fails.
The binary majority proof depended on a uniform binary selected age
being the global strict majority; a selected common translation of two
different ternary ages has no such implication.

For the lower bound on all codes, consider the four vectors

$$
000,\qquad 110,\qquad 211,\qquad 222.
\tag{NAR.13.19}
$$

In their displayed order, the larger-minus-smaller coordinate difference
vectors for the six pairs are
$110,211,222,101,112,011$. Each contains a common nonzero displacement
at least twice: respectively $1,1,2,1,1,1$. All six pairs are native
conflict edges, with genuine positive-lag whole-row witnesses supplied
by (NAR.13.8). They form a four-clique and force four values regardless
of the code's symmetry. The upper bound is Theorem 13.4's two retained
fixed coordinates, using nine attained values. Failure of the symmetric
codes is thus separate from the lower bound for arbitrary codes. The
four-clique rules out three values for every code. No code attaining four
values, or proof that nine are necessary, is supplied. $\square$

**Proposition 13.8 (a valid binary diameter comparison).** For $H=1$ and
$2(k-1)<r$, the native price satisfies the additional lower bound

$$
N_1(r,k)\ \ge\
\left\lceil\frac{2^r}{\displaystyle\sum_{j=0}^{k-1}\binom rj}\right\rceil.
\tag{NAR.13.20}
$$

This bound can exceed the disjoint-block bound: at $r=6,k=2$ it gives
$N_1(6,2)\ge10$, whereas the latter gives only eight. A maximum
permissible color-class size does not supply an optimal coloring.

**Proof.** Identify a binary vector with its support $A\subseteq I$.
For two supports $A,B$, the positive and negative displacement counts
are $|A\setminus B|$ and $|B\setminus A|$. Therefore a color class must
satisfy, for every pair in it,

$$
|A\setminus B|\le k-1,\qquad |B\setminus A|\le k-1.
\tag{NAR.13.21}
$$

Equivalently its diameter in
$d_{\rm as}(A,B)=\max(|A\setminus B|,|B\setminus A|)$ is at most $k-1$.
This is a maximum-distance condition on an anticode, not the
minimum-distance condition of an error-correcting code. It implies
Hamming diameter at most $2(k-1)$, since Hamming distance is the sum of
the two directed differences. The converse implication is false in
general: $\varnothing$ and a two-element set have Hamming distance two
but directed maximum two, so at $k=2$ they cannot share a color.
One cannot identify the native independent classes with all Hamming
anticodes of that diameter.

Use only the forward implication and
[Huang--Klurman--Pohoata, *On subsets of the hypercube with prescribed
Hamming distances*, arXiv:1812.05989v1, Theorem 1.1](https://arxiv.org/html/1812.05989v1).
Its hypotheses are binary vectors of length $n$ with all pairwise
Hamming distances at most $d<n$; for $d=2t$ it bounds size by
$\sum_{j=0}^{t}\binom nj$. Here the exact substitutions are
$n=r$, $t=k-1$, $d=2(k-1)<r$. Every color class consequently has at most
the denominator in (NAR.13.20) members. Partitioning all $2^r$ vectors
into $N$ classes yields that bound. This known diameter theorem is an
intermediate literature-attested supplier, not a new theorem claimed
here. At $r=6,k=2$, the denominator is $1+6=7$ and
$\lceil64/7\rceil=10>2^3$.

The zero-centered Hamming ball of radius $k-1$ satisfies (NAR.13.21):
each support has size at most $k-1$, so each directed difference does too.
It is therefore a native independent class of the denominator's size.
Thus the size upper bound is attained by this one class, without asserting
a disjoint covering of the whole cube by equally large classes. For
$r=3,k=2$ it is four, and the two classes of the majority code happen to
attain a full partition; the $r=6,k=2$ lower bound makes no analogous
partition assertion.

For $H>1$, disagreements can have several nonzero magnitudes. The edge
criterion in (NAR.13.4) counts each exact displacement separately.
It is not a threshold on the number of positive differences or on
Hamming distance. Already at $H=2,r=2,k=2$, $00$ and $12$ differ in
both coordinates and in one sign direction, but have no repeated
nonzero displacement and hence are nonadjacent. Thus the binary
asymmetric-distance correspondence does not extend merely by using the
same name or replacing the alphabet. No asymmetric-anticode or
set-family extremum is imported with unmatched parameters. $\square$

**Mathematical citation 13.9 (suppliers and the retained-resource boundary).**
The native algebra and complete record are Definitions 1.1--1.2 and the
cited `literalRecord`, `canonicalRow_record_iff`, `legal_values_row` and
`rowFiberEquiv`. The clock used here is the right clock $c$, with
`right_clock_iterate` from
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean).
It is not numerically identified with the intrinsic inverse depth $\nu$.
The finite separated-age source family, initial-row acquisition factor
and singleton entire-row mechanism are from
[published §11](https://github.com/the-omega-institute/trureturing/blob/d32f66a819e5fa524c1d876fb69c8a4dad3fd343/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md#11-retaining-a-reference-before-the-future-cut-is-known).
Section 12 concerns multiple acquired and retained chronological rows;
no result from its component theorem is a premise for the single-code,
single-later-row task here.

The graph coding bridge belongs to Transport--Memory Completion §8.2,
which cites H. Witsenhausen, *The zero-error side information problem and
chromatic numbers (Corresp.)*, IEEE Transactions on Information Theory
22(5), 592--593, [doi:10.1109/TIT.1976.1055607](https://doi.org/10.1109/TIT.1976.1055607).
Theorem 13.3 explicitly supplies both directions for the present target;
no detailed historical full-text theorem is needed beyond that reused
finite argument. Charpenay--Le Treust--Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*, arXiv:2211.03649v2, Definitions II.1 and IV.5 and Theorem
IV.8](https://arxiv.org/html/2211.03649v2), defines edges by differing
function values at a common feasible side-information value. That is
the relevant mature coding relation. Its rates use i.i.d. source laws,
expected prefix-code lengths and asymptotic blocks; these hypotheses do
not provide an exact adversarial single-record alphabet price here.
The only imported combinatorial inequality is Theorem 1.1 of the cited
Huang--Klurman--Pohoata version, with the strict diameter hypothesis
verified in Proposition 13.8. Its Hamming-class size conclusion is not
an exact chromatic formula.

The latest compared immutable public suppliers have different contracts.
[Native Birth Provenance §9](https://github.com/the-omega-institute/trureturing/blob/a56175a1ce5884e0aa6f7e4ff3109dfaaecdd4a3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#9-repeated-partners-on-a-complete-depth-three-one-image-fiber)
asks for a predecessor row after exactly one authenticated update, with
acquired current hidden-class values and fresh stationary queries. Its
repeated partners constrain that image fiber; it supplies no unknown-lag
future-menu code. [Boundary Geometry V §114](https://github.com/the-omega-institute/trureturing/blob/a56175a1ce5884e0aa6f7e4ff3109dfaaecdd4a3/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_V.md#114-static-linear-transport-across-an-actual-accepted-rho-step)
compares time-independent real-linear heat transport on all-occurrence
signed-state spaces. Its semigroup clocks and linear ranks are neither
unknown native update counts nor finite retained alphabets.

The substantive conclusions here are the complete native $k$-slot
collision criterion, its binary visibility threshold and matched
half-boundary price, the finite-age bounds and actual ternary
obstructions. They are repo-derived ordinary deductions using the
stated suppliers and known coding methods, without a worldwide
originality assertion or new kernel verification. The remaining general
chromatic values, including $N_2(3,2)$ within (NAR.13.17), are undetermined
by these results. An arbitrary restricted menu requires its own collision
analysis; no all-menu classification is supplied.

The price is the number of exported retained values, or its fixed-width
binary representation. Even a one-value code does not price source
storage, acquired rows, installed decoder controls, tree parsing,
arithmetic widths, workspace, public addresses or transmission. Paid
acquisition, code export and discard, stationary capture, permissions,
lawful handoffs and genuine continuation remain premises or separately
priced resources. A code can recover $\ell$ while many initial vectors
remain compatible, so recovery does not certify source identity or the
history. No acquisition optimum, physical-memory optimum, physical
elapsed-time statement, native update service or unrestricted-source
majority code follows from this finite-family theorem.

## 追加锚（本行以下为增补区）

## 14. Public future regions, relational reference memory and causal lag ambiguity

**Assumption 14.1 (an arbitrary public menu before encoding).** Keep the
native ordered trees, homomorphic $\rho$, complete rows, public $P,D,H$
and original depth-$D$ indices of Assumption 13.1. Thus $b=H+1$,
$I=\{j:w_j\in A_D(P)\}$ and the source domain is precisely

$$
X_a=\mathcal B_D[(T_{jb+a_j})_{0\le j<2^D}],\qquad
T_n=\rho^n\alpha,\qquad
a\in\{0,\ldots,H\}^{I},\quad a_j=0\ (j\notin I).
\tag{NAR.14.1}
$$

Fix a nonempty finite family $\mathcal M$ of nonempty subsets of $I$.
Its members are possible future visible regions, not simultaneously
acquired records. For $S\in\mathcal M$ set
$Q_S=W_D\setminus\{w_i:i\in S\}$. The menu is public before encoding;
its member is selected only after export and discard. The elapsed native
update lag remains unknown and must be recovered from the supplied
inputs. Write $\lambda_0=0$ for nonnegative lags or
$\lambda_0=1$ for strictly positive lags, and
$L_{\lambda_0}=\{\lambda_0,\lambda_0+1,\ldots\}$. The contract is

$$
\exists E,\mathsf{Dec}\quad\forall a\quad\forall S\in\mathcal M
\quad\forall\ell\in L_{\lambda_0}:\qquad
\mathsf{Dec}\bigl(S,E(R_P(X_a)),R_{Q_S}(\rho^\ell X_a)\bigr)=\ell.
\tag{NAR.14.2}
$$

The encoder receives only the genuinely acquired initial row, exports
one code and discards that row before selection of $S$. Every surviving
source-bearing distinction counts as code, including source identifiers,
epochs, clocks, sizes, logs, pointers, allocation distinctions and
archives. The decoder receives the public constants, $S$, that code and
exactly the complete later acquired row: its literal exterior, labels,
brackets, reached/absent guards and every within-row hidden equality
and disequality. No hidden value, cross-row hidden comparison or free
source profile is supplied. Acquisition, export/discard, stationary
capture, permissions and genuine same-source, same-root, pure-$\rho$
continuation remain the premises of Assumptions 10.1, 11.1 and 13.1.

Let $N_H(\mathcal M)$ be the minimum number of attained retained code
values in (NAR.14.2). Its fixed-width binary representation price is
$\lceil\log_2N_H(\mathcal M)\rceil$. These units exclude source storage,
acquisition, decoder controls, arithmetic width, working space and
physical elapsed time. The finite independent-age source promise is
part of the contract, not a reduction of all native sources to ages.

**Reuse 14.2 (complete native collisions and the acquired-row factor).**
Apply Theorem 13.3 separately at $k=|S|$ for every $S\in\mathcal M$.
The original offsets $jb$ remain unchanged. Its entire-row equivalence is

$$
R_{Q_S}(\rho^\ell X_a)=R_{Q_S}(\rho^{\ell'}X_{a'})
\quad\Longleftrightarrow\quad
 a_i+\ell=a'_i+\ell'\quad(i\in S).
\tag{NAR.14.3}
$$

Every such cut is allowed: a ray through any selected exposed word has
no prefix in $P\cup Q_S$. This includes $D=0$, where the only selected
region is the root and $Q_S=\varnothing$. In the separated-age family
all depth-$D$ slots are reached. The literal exterior is the unchanged
ordered skeleton with displayed $T_{ib+a_i+\ell}$ at selected slots and
address-marked holes elsewhere. Hidden exponents at different original
indices belong to disjoint intervals $[jb+\ell,jb+H+\ell]$; their
complete partition is discrete at every lag. Consequently (NAR.14.3)
preserves every exterior label and bracket, every cut guard and all
within-row hidden comparisons, not merely a clock summary. Absent
addresses inside a displayed tree remain determined by its literal
shape. No hidden-visible comparison is included in the row contract.

The induced conflict graph on $\{0,\ldots,H\}^{I}$ has the inherited
edge relation

$$
a\sim_{\mathcal M}a'
\quad\Longleftrightarrow\quad
\exists S\in\mathcal M\ \exists d\in\mathbb Z\setminus\{0\}:\quad
 a_i-a'_i=d\quad(i\in S).
\tag{NAR.14.4}
$$

For each such edge the two legal lags

$$
\ell=\lambda_0+\max(0,-d),\qquad
\ell'=\lambda_0+\max(0,d)
\tag{NAR.14.5}
$$

have difference $d$ and give equal complete rows at the selected $S$.
Both are positive if $\lambda_0=1$. Each history is the pure-$\rho$
continuation of its own fixed actual native source; no histories are
spliced. Thus the two lag conventions give the same conflict graph.

The same initial-row factor (NAR.13.9) computes every exposed age:

$$
a_i=c(X_a|_{w_i})-ib
 =\gamma_{P,w_i}(R_P(X_a))-s(w_i)-ib.
\tag{NAR.14.6}
$$

Here $c$ is the supplied right clock, with $c(T_n)=n$, not the intrinsic
inverse depth $\nu$. Hence every finite function $e(a)$ is implementable
as $E(R_P(X_a))=e(a)$ using just the initial acquired literal exterior.

Reuse Theorem 13.3 and Transport--Memory Completion §8.2: the code is
sufficient exactly when $e$ separates every edge in (NAR.14.4), so
$N_H(\mathcal M)=\chi(G_{H,\mathcal M})$. This is the existing finite
zero-error coloring bridge, not a new general coding theorem. Its
terminating decoder parses the later literal subtrees to obtain
$z_i=c((\rho^\ell X_a)|_{w_i})-ib$. Enumerate the finite age vectors
$u$ with the received code; for one public $i_0\in S$ retain
$h=z_{i_0}-u_{i_0}$ exactly when $h\ge\lambda_0$ and
$z_i-u_i=h$ throughout $S$. The genuine vector survives. Two surviving
vectors giving different lags would violate properness, so return their
unique common lag. Equivalently one may compare the constructed full
rows, using (NAR.14.3). This recovers the lag without requiring a unique
initial vector; unpromised inputs may fail.

Only inclusion-minimal members of $\mathcal M$ matter. Every menu
member contains one, and a constant displacement on a larger member
already holds on that smaller member. Deleting nonminimal members
therefore preserves the graph and retained-code price. It preserves
packing and transversal numbers below as well: a hitting set for all
minimal members hits every member, and each disjoint packed member can
be replaced by a contained minimal member without losing disjointness.

**Theorem 14.3 (binary memory is exactly controlled by pairwise overlap).**
Under Assumption 14.1 with $H=1$,

$$
N_1(\mathcal M)=2
\quad\Longleftrightarrow\quad
S\cap T\ne\varnothing\quad(S,T\in\mathcal M).
\tag{NAR.14.7}
$$

If two members are disjoint, $N_1(\mathcal M)\ge4$. No binary menu in
this contract has optimum three. In the intersecting case an effective
one-bit encoder, factoring through (NAR.14.6), is

$$
e(a)=1\quad\Longleftrightarrow\quad
\exists T\in\mathcal M:\ a_i=1\quad(i\in T).
\tag{NAR.14.8}
$$

**Proof.** This is the monotone winning-set predicate generated by the
menu. Pairwise intersection makes it proper: if a set of one positions
contains a menu member, its complement contains none. These are the
mature simple-game notions of Valentiner--Volić, Definitions 2.1 and
2.6; the assertion here concerns the native retained-lag task.

On a binary conflict, the only nonzero displacements are $1$ and $-1$.
In one orientation $a$ is all one on a selected $S$, whereas $a'$ is all
zero there. The first vector has code one. Every $T\in\mathcal M$
meets $S$, so the second vector has a zero somewhere in $T$ and has code
zero. Reversing orientation gives the same separation. The code is
proper; all-zero and all-one vectors attain both labels and are adjacent,
so the price is exactly two.

There is also a direct decoder. For the acquired normalized values
$z_i=a_i+\ell$ on $S$, if they are nonuniform, their two values are
$\ell,\ell+1$; return $\min_{i\in S}z_i$. If they are uniform at $t$,
the selected ages are all one or all zero. All one forces $e(a)=1$;
all zero prevents every menu member from being all one by intersection
and forces $e(a)=0$. Return $t-e(a)$. The answer has the allowed sign
on promised inputs, including singleton $S$ and both lag conventions.

Conversely, take disjoint nonempty $U,V\in\mathcal M$. The four age
vectors $a^{xy}=x\mathbf1_U+y\mathbf1_V$, $x,y\in\{0,1\}$, fix all
other ages to zero. Any two distinct vectors have a constant nonzero
displacement on $U$ or $V$; they form a four-clique. Formula
(NAR.14.5) supplies actual complete-row witnesses for all six edges.
Four distinct retained labels are necessary. This proves the converse
and excludes a three-label optimum. $\square$

**Proposition 14.4 (overlap edge cases in the native contract).** A
singleton menu $\{S\}$ has price $H+1$, for any nonempty $S$ and any
$H\ge0$, as supplied by Theorem 13.4. At $H=1$, a common exposed
position in every member allows retaining its one acquired age bit;
a common position is unnecessary. A menu of singleton positions has
price $2^t$ when it contains $t$ distinct positions. A connected menu
intersection graph does not suffice for two labels.

**Proof.** For a common position $i_*$, use $z_{i_*}-a_{i_*}$, a direct
special case of (NAR.14.6) and the supplied decoder. For the three-member
menu $\{\{0,1\},\{0,2\},\{1,2\}\}$, pairwise intersections are
nonempty but the triple intersection is empty. Theorem 14.3 still gives
two labels. It is realized natively at $D=2$, $P=\{RR\}$, with original
exposed indices $0,1,2$, not by renumbering native offsets.

For $t$ distinct singleton members, all $2^t$ independent choices on
those positions form a clique; retaining those bits suffices. This
includes one singleton and, at $D=0$, the single root position. For
connectedness alone use $\mathcal M=\{\{0\},\{0,1\},\{1\}\}$ in the
same depth-two family. Its intersection graph is connected, but its
minimal members are the disjoint singletons. The price is exactly four.
Section 12's connectedness concerns several acquired chronological
rows, not one code exported before a future region is selected. $\square$

**Theorem 14.5 (packing, coordinate retention and justified spatial classes).**
Let $\nu(\mathcal M)$ be the largest number of pairwise disjoint menu
members and $\tau(\mathcal M)$ the least size of a public set
$F\subseteq I$ meeting every member. Then

$$
b^{\nu(\mathcal M)}\le N_H(\mathcal M)\le b^{\tau(\mathcal M)}.
\tag{NAR.14.9}
$$

For $H\ge1$, losslessly retaining a fixed public coordinate tuple
$(a_i)_{i\in F}$, up to injective relabeling, is sufficient exactly when
$F$ is a transversal. The exact minimum within this restricted class
is $b^{\tau(\mathcal M)}$ labels, or
$\lceil\tau(\mathcal M)\log_2 b\rceil$ fixed-width bits. Arbitrary
functions of all acquired ages are not this tuple-retention class.
For $H=0$, no coordinates are needed and $N_0(\mathcal M)=1$.

Whenever $\nu=\tau$, fixed-coordinate retention is optimal among all
codes. In particular this holds if every menu member is an interval in
the public increasing order of $I$, or if the menu is laminar: two
members are disjoint or one contains the other. In either class,

$$
N_H(\mathcal M)=b^{\nu(\mathcal M)}=b^{\tau(\mathcal M)}.
\tag{NAR.14.10}
$$

**Proof.** For a disjoint packing $S_1,\ldots,S_\nu$, assign one
independent constant age from $\{0,\ldots,H\}$ to each entire $S_j$,
fixing all other ages to zero. The $b^\nu$ vectors form a clique:
any two differ by a nonzero constant on at least one packed member.
Reuse (NAR.14.3)--(NAR.14.5) for their complete native witnesses. This
is the block-clique mechanism of Theorem 13.4 applied to the actual menu.

For a transversal $F$, retain its acquired ages by (NAR.14.6). Upon
selection of $S$, choose its least index in $F\cap S$ and return
$z_i-a_i$. This gives $b^{|F|}$ attained labels, since all ages on $F$
are independent. If $H\ge1$ and $F$ misses a member $S$, the vectors
$0$ and $\mathbf1_S$ agree on $F$ but conflict on $S$. Their identical
tuple cannot decode the unequal legal lags from (NAR.14.5). Thus a tuple
is sufficient exactly when it hits the menu, proving its exact price.
For $H=0$ the unique vector gives $z_i=\ell$ on every selected region;
the empty tuple suffices. The bounds also equal one in that case.

The spatial steps are mature packing/piercing arguments, used here
inside the native memory conclusion. For finite nonempty intervals in
the public order, repeatedly choose a remaining interval with smallest
right endpoint, retain that endpoint, and remove every interval
containing it. Each surviving interval has right endpoint no smaller
and does not contain the chosen point, so its left endpoint is strictly
to the right. The chosen witness intervals are consequently pairwise
disjoint; the retained endpoints hit all intervals. If the procedure
chooses $p$ intervals and $p$ points, then
$p\le\nu\le\tau\le p$, giving equality. Gyárfás--Lehel, printed
pp. 571--573, records the single-interval equality and credits
Hajnal--Surányi; only this finite single-interval case is used here.

For a finite laminar menu, its inclusion-minimal members are disjoint
and every member contains one. If there are $p$ minimal members, they
supply a packing of size $p$ and choosing one point from each supplies
a transversal of size $p$. Again $p\le\nu\le\tau\le p$. Substitution
in (NAR.14.9) proves (NAR.14.10).

The public order in the interval argument is inherited from the
original lexicographic $w_j$ order, with no change to $jb$. Exposed
depth-$D$ descendants of a single prefix form a consecutive interval
in this order: all words with that prefix are consecutive, and deleting
nonexposed words preserves that property among exposed words. For a
family of such nonempty prefix regions, prefix comparison also makes
them laminar. Thus these native cylinder regions meet the hypotheses.
Arbitrary sets of addresses or unions of cylinders need not do so.
The condition $\nu=\tau$ is sufficient for coordinate optimality;
no converse characterization of all coordinate-optimal menus follows.
$\square$

**Theorem 14.6 (an empty triple intersection costs an extra multilevel label).**
If $H\ge2$ and $U,V,W\in\mathcal M$ satisfy
$U\cap V\cap W=\varnothing$, then

$$
N_H(\mathcal M)\ge H+2.
\tag{NAR.14.11}
$$

In particular, $H+1$-label sufficiency at $H\ge2$ requires every three
menu members to intersect. This is a necessary condition, with no
converse or general higher-intersection classification asserted.

**Proof.** On the exposed indices define the two actual age vectors

$$
B_i=\mathbf1_V(i),\qquad
A_i=\begin{cases}
B_i+1,&i\in W,\\
1,&i\in U\setminus W,\\
0,&i\notin U\cup W.
\end{cases}
\tag{NAR.14.12}
$$

All entries lie in $\{0,1,2\}$. For $i\in U\cap W$, the empty
triple intersection gives $i\notin V$, so $A_i=1$. Thus $A=1$ on
$U$, $B=1$ on $V$, and $A-B=1$ on $W$. Alongside $A,B$ take the $H$
constant vectors $C_t$, $t\in\{0,\ldots,H\}\setminus\{1\}$.
They are all distinct: $A$ and $B$ take value one on nonempty $U$ and
$V$, and $A-B=1$ on nonempty $W$. Any two constants conflict on any
menu member; $A$ conflicts with each $C_t$ on $U$ by displacement
$1-t$, and $B$ with each $C_t$ on $V$ by the same displacement.
Finally $A$ and $B$ conflict on $W$. These are $H+2$ pairwise adjacent
vectors. Equation (NAR.14.1) realizes each as a finite native source,
and (NAR.14.3)--(NAR.14.5) realize every edge with complete equal rows
at unequal legal lags. The clique forces (NAR.14.11). $\square$

**Proposition 14.7 (one depth-three Fano menu separates three memory prices).**
Take $D=3$, $P=\{RRR\}$ and the original exposed indices
$I=\{0,\ldots,6\}$. Let the menu be

$$
\mathcal M_F=\{012,034,056,135,146,236,245\},
\tag{NAR.14.13}
$$

where a three-digit word denotes its set of indices. Then
$\nu(\mathcal M_F)=1$, $\tau(\mathcal M_F)=3$, and

$$
N_1(\mathcal M_F)=2,\qquad
H+2\le N_H(\mathcal M_F)\le(H+1)^3\quad(H\ge2).
\tag{NAR.14.14}
$$

For binary ages this is one bit of relational reference memory versus
three bits for a lossless fixed-coordinate tuple. In particular
$4\le N_2(\mathcal M_F)\le27$; the exact ternary optimum is unresolved
by these results.

**Proof.** Each pair of points occurs in exactly one listed line, and
each point occurs in three lines. Each line therefore intersects the
other six lines once: its three points each meet two other lines, with
no repetitions because two common points would repeat a point pair.
Hence $\nu=1$. Two points together meet exactly $3+3-1=5$ of the seven
lines and cannot hit all seven; a whole line does hit all of them.
Therefore $\tau=3$. Theorem 14.3 gives the binary price, and Theorem
14.5 gives the tuple price $2^3=8$ and the general upper bound.

The three members $U=012$, $V=034$, $W=135$ have empty triple
intersection. Theorem 14.6 gives the lower bound; its explicit vectors
are $A=1112010$ and $B=1001100$ in the original index order. For a
complete native unequal-positive-lag witness at $H=2$, keep $b=3$,
the eighth age fixed to zero and all original offsets. The actual
initial sources are

$$
\begin{aligned}
X_A&=\mathcal B_3[T_1,T_4,T_7,T_{11},T_{12},T_{16},T_{18},T_{21}],\\
X_B&=\mathcal B_3[T_1,T_3,T_6,T_{10},T_{13},T_{15},T_{18},T_{21}].
\end{aligned}
\tag{NAR.14.15}
$$

Select $S=W=135$. The histories $(X_A,\ell=1)$ and $(X_B,\ell'=2)$
have the same full exterior

$$
\left\langle
 \left\langle
  \langle\square_{LLL},T_5\rangle,
  \langle\square_{LRL},T_{12}\rangle
 \right\rangle,
 \left\langle
  \langle\square_{RLL},T_{17}\rangle,
  \langle\square_{RRL},\square_{RRR}\rangle
 \right\rangle
\right\rangle.
\tag{NAR.14.16}
$$

The five hidden values, in their original hole order, are respectively
$(T_2,T_8,T_{13},T_{19},T_{22})$ and
$(T_3,T_8,T_{15},T_{20},T_{23})$. Within either row they are all
unequal, every hole is reached and every reflexive comparison is true.
All exterior labels, brackets and absent-address replies agree because
the displayed literal trees agree. Thus these are identical entire rows,
including every hidden disequality, at distinct strictly positive lags.
The initial acquired row displays all seven independent ages and hides
only slot seven; (NAR.14.6) gives the encoder its data without supplying
an age oracle. The other clique edges are complete native witnesses by
Reuse 14.2, not just abstract graph edges. $\square$

**Theorem 14.8 (one later row has a smaller ambiguity than one pre-menu code).**
For a promised whole later row $Y$ at $S\in\mathcal M$, let
$z_i=c(Y|_{w_i})-ib$. Without the retained code its compatible lag answers
are exactly the integer interval

$$
\mathcal L(Y,S)=
\left[\max\left(\lambda_0,\max_{i\in S}(z_i-H)\right),
             \min_{i\in S}z_i\right]\cap\mathbb Z.
\tag{NAR.14.17}
$$

Its size is at most $H+1$, and the maximum over promised entire rows is
exactly $H+1$. Every individually fixed, preannounced $S$ has retained
price $H+1$, as in Theorem 13.4, but a single code chosen before selection
of $S$ can require strictly more. The Fano menu at $H\ge2$ does so.

**Proof.** A compatible history with lag $h$ has selected ages
$a_i=z_i-h\in\{0,\ldots,H\}$ and $h\ge\lambda_0$, yielding exactly
the inequalities in (NAR.14.17). Conversely, for any integer satisfying
them choose these ages on $S$ and any legal ages, for example zero, on
$I\setminus S$. Keep all other original slots at age zero. This is an
actual source (NAR.14.1); its later selected literal trees have precisely
the received exponents. The promised row and (NAR.14.3), including the
complete hidden partition, give equality of the entire row $Y$.
This proves sufficiency for every integer in the interval, not only for
a scalar projection of $Y$.

For one selected index, $z_i-H\le h\le z_i$ contains $H+1$ integers;
intersecting such intervals and the legal-lag half-line cannot add any.
To attain all $H+1$, take selected normalized values constantly
$H+\lambda_0$. For each
$h\in\{\lambda_0,\ldots,H+\lambda_0\}$ assign selected ages
$H+\lambda_0-h$, fixing other exposed ages to zero. These histories
share one entire later row and have all $H+1$ distinct answers. The
maximum is therefore exact; a nonuniform or near-origin row can have
fewer answers. A preannounced fixed region permits retaining one of
its ages; the same uniform-row witnesses force $H+1$ labels.

In the Fano menu Theorem 14.6 requires at least $H+2$ labels from one
encoder working for every possible future region, although no one
later row has more than $H+1$ compatible lag answers. For $H=2$ this is
a strict label gap, with no forced rounded-bit gap: three and four
labels both fit in two fixed-width bits. At $H=3$ the four local answers
fit in two bits, while at least five retained labels require at least
three bits. The local numbering of answers is available after $S,Y$;
it cannot replace a function of the initial row exported beforehand.
This is the causal compatibility distinction of Transport--Memory
Completion §8.4, with a new native menu obstruction.

There is no conflict with
`minimum_repair_labels_eq_chromatic_eq_fiber_diversity` in the supplied
[DefectGraphMinimumColoring](../../../D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean).
That statement uses a deterministic record and target on one finite
state domain and allows a label depending on that full state. Here the
later record is not a deterministic function of $a$ alone: it also
varies with future $S$ and $\ell$. Enlarging the state to
$(a,S,\ell)$ makes the readout deterministic, but the allowed label must
still factor through $a$, by (NAR.14.6); the supplier does not impose
that factorization. It would allow different labels for the same $a$
under different future choices. Unbounded lags also exceed its finite
domain premise, and restricting to a finite witness domain does not
remove the factorization mismatch. Thus its unrestricted fiber formula
does not give a causally available $(H+1)$-label encoder here.
An internal observer must preserve distinctions across the allowed
future regions before discarding its initial row. The maximum ambiguity
of any later record alone does not determine that retained resource.
$\square$

**Mathematical citation 14.9 (reuse, literature and conclusion boundaries).**
The native source and row suppliers are Definitions 1.1--1.2, with
`literalRecord`, `canonicalRow_record_iff`, `legal_values_row` and
`rowFiberEquiv`; the right-clock supplier is `right_clock_iterate` in
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean).
Section 11 supplies the separated-age family and acquired-row factor;
§13.3 supplies the entire-row collision criterion and effective decoder.
For the uniform menu of all $k$-subsets, the packing and transversal
numbers in Theorem 14.5 are $\lfloor r/k\rfloor$ and $r-k+1$, recovering
§13.4. Pairwise intersection is then equivalent to $2k>r$, recovering
§13.5. Section 12 instead concerns multiple acquired chronological rows;
its connectedness criterion is not used to infer a pre-menu code.
The generic coloring and causal local-versus-retained distinction belong
to [Transport--Memory Completion §§8.2 and 8.4](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#82-标签恰须切开可能混淆的前缀).

The Boolean predicate used inside Theorem 14.3 is a standard proper
simple game, in the precise terminology of Valentiner--Volić,
[*The topology of simple games*, arXiv:2503.12578v1,
Definitions 2.1 and 2.6](https://arxiv.org/html/2503.12578v1).
The finite single-interval packing/piercing step inside Theorem 14.5
is literature-attested in Gyárfás--Lehel,
[*A Helly-type problem in trees*, printed pp. 571--573 and reference [1]
on p. 584](https://users.renyi.hu/~gyarfas/Cikkek/02_GyarfasLehel_AHellyTypeProblemInTrees.pdf).
Their statement credits Hajnal--Surányi's 1958 paper; no independently
inspected theorem from that original paper or from their multi-interval
results is required. The displayed greedy argument verifies the discrete
public-order hypotheses here. Proper-game terminology, finite coloring
and interval duality are reused ingredients, not new inventions.

Charpenay--Le Treust--Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*, arXiv:2211.03649v2, Definitions II.1 and IV.5](https://arxiv.org/html/2211.03649v2),
uses differing function values at a common feasible side-information
value to define the relevant conflict. Its source model is i.i.d., its
objective is expected prefix-code length across asymptotic blocks, and
its rate conclusions have additional support hypotheses. Those results
do not furnish this exact adversarial single-row alphabet price. The
finite coding bridge is already supplied by §13.3 and Transport §8.2;
no external rate formula is transferred.

The new native deductions are the arbitrary-menu overlap criterion,
its acquired-row encoder and decoder, the exact tuple-retention price
and its justified spatial cases, the empty-triple-intersection
obstruction, and the Fano causal separation from whole-row ambiguity.
They are repo-derived ordinary-theory results with stated reusable
ingredients, without a worldwide originality or kernel-verification
claim. General multilevel menu prices, a converse to Theorem 14.6 and
the exact Fano ternary optimum remain undetermined here.

These are finite-family retained-label and fixed-width representation
statements. Acquired rows, truthful export/discard, actual continuity,
stationary capture, permissions and lawful handoff remain premises.
Recovery of an update count does not certify source identity or history,
perform acquisition, grant native updates or price their execution.
No all-source menu theorem, physical or total/peak memory bound,
working-space optimum or physical-time recovery follows.

## 追加锚（本行以下为增补区）

## 15. Intersection heights, native reference codes and uniform arbitrary-label converses

**Assumption 15.1 (intersection order on the separated-age family).** Retain
Assumption 14.1, the complete-row equivalence (NAR.14.3), the native conflict
relation (NAR.14.4) and the acquired-row factor (NAR.14.6). Put
$q=H+1$ and $A_H=\{0,\ldots,H\}^{I}$. A finite menu $\mathcal M$ is
$q$-wise intersecting when every nonempty subfamily of at most $q$ members
has nonempty intersection. Equivalently, every $q$-tuple of menu members,
with repetitions allowed, has nonempty intersection. Repetitions are part of
the definition: they make the condition meaningful when the menu has fewer
than $q$ members.

The encoder uses the genuinely acquired initial row and exports the code
before the future member $S$ and lag are chosen, then discards that row.
The only later inputs are
the code, the public controls and $S$, and the complete later row specified
in Assumption 14.1. Its guards and hidden equality/disequality partition are
included. All surviving source-bearing distinctions count toward the code;
there is no additional Read, hidden-value, source or epoch oracle. Both lag
conventions and the genuine same-source pure-$\rho$ histories of that
assumption remain in force. A code's labels have no prescribed order.

For $a,b\in A_H$, write $a\mathrel{\to_+}b$ when some $S\in\mathcal M$
and some integer $d>0$ satisfy $b_i-a_i=d$ for every $i\in S$. Write
$a\mathrel{\to_<}b$ when some $S\in\mathcal M$ satisfies $a_i<b_i$ for every
$i\in S$. These are relations between alternative initial age profiles. They
are not the evolution of one actual source under $\rho$: a path may reset
coordinates outside its witnessing region, whereas actual $\rho$ advances
every original slot. The relation $\to_+$ is contained in $\to_<$. Without
pairwise intersection the relations are directed graphs and may contain both
opposite arcs.

**Theorem 15.2 (uniform intersection reference and its effective decoder).**
If $\mathcal M$ is $q$-wise intersecting, then the minimum retained alphabet is

$$
N_H(\mathcal M)=q.
\tag{NAR.15.1}
$$

Both $\to_+$ and $\to_<$ are acyclic. Their longest-path ranks agree, and
the common rank is the following finite expression:

$$
E(a)=\max\left(\{0\}\cup
 \left\{m\in\{1,\ldots,H\}:\begin{array}{l}
 \exists S_1,\ldots,S_m\in\mathcal M\text{ such that for every }1\le j\le m,\\[-2pt]
 \displaystyle\bigcap_{h=m-j+1}^{m}S_h
 \subseteq\{i\in I:a_i\ge j\}
 \end{array}\right\}\right).
\tag{NAR.15.2}
$$

The encoder is $e(a)=E(a)$, with labels $0,\ldots,H$. It factors through the
acquired initial row by (NAR.14.6). Given a code value, a selected
$S\in\mathcal M$ and a complete later row, the decoder of Reuse 14.2
enumerates the finitely many $u\in A_H$ with $E(u)=e(a)$, computes the
normalized displayed values $z_i$, and retains precisely those candidates for
which

$$
h=z_{i_0}-u_{i_0}\ge\lambda_0,\qquad z_i-u_i=h\quad(i\in S),
\tag{NAR.15.3}
$$

for one public $i_0\in S$. Every surviving candidate gives the same $h$, and
that $h$ is the recovered lag.

**Proof.** Suppose first that a $\to_<$ walk has $q$ edges, witnessed by
$S_1,\ldots,S_q$. Their intersection contains some $i$, by $q$-wise
intersection, and the $i$-coordinate increases strictly at all $q$ steps. It
cannot stay in $\{0,\ldots,H\}$, whose height is $q-1$. Hence there is no
$q$-edge walk, and in particular no directed cycle (a cycle could be
repeated). The same holds for $\to_+$.

Let $R_<(a)$ and $R_+(a)$ be the maximum numbers of edges in paths ending at
$a$. A path ending at the constant vector $C_t=(t,\ldots,t)$ has length at
most $t$: its length is at most $H$ by the preceding paragraph, so the
intersection of all its witnessing regions is nonempty and one common
coordinate has increased by at least one per edge. The chain
$C_0\to_+C_1\to_+\cdots\to_+C_H$ shows that every value $0,\ldots,H$ is
attained by both ranks. Those constants are also pairwise adjacent: every
pair has a nonzero constant displacement on any nonempty menu member.
Thus any proper code has at least $q$ values.

For a path of length $m$ ending at $a$, every coordinate in the intersection
of the last $j$ witnessing regions has increased at least $j$ times. This is
exactly the suffix condition in (NAR.15.2), so every path gives an admissible
sequence there. Conversely, suppose $S_1,\ldots,S_m$ satisfies that condition. Set
$x^m=a$ and, for $k=m,\ldots,1$, define

$$
x^{k-1}_i=
\begin{cases}
x^k_i-1,&i\in S_k,\\
H,&i\notin S_k.
\end{cases}
\tag{NAR.15.4}
$$

The selected coordinates in (NAR.15.4) are nonnegative. Indeed, if $i$ is
absent from a later witnessing set, the backward construction has reset it to
$H$ and performs at most $m-1\le H-1$ later decrements; if it remains in all
later sets, the corresponding suffix condition supplies the required lower
bound on $a_i$. Thus every $x^k$ lies in $A_H$, and
$x^{k-1}\to_+x^k$ with displacement $1$ on $S_k$. This proves
$R_+(a)=E(a)=R_<(a)$.

If $a\to_<b$, appending that edge to a longest path gives
$E(a)<E(b)$. This holds in particular on every $\to_+$ edge, so $E$ is a
proper code for the native conflict graph. The
complete-row equality and the two legal lag choices in (NAR.14.3)--(NAR.14.5)
are therefore separated by this code. Formula (NAR.14.6) supplies its input;
the candidate test (NAR.15.3) is exactly the finite decoder already justified
there. A genuine candidate survives. Two candidates with different lags
would be a conflict edge carrying one code, which is impossible. The lower
bound from the constants and this upper bound prove (NAR.15.1). The finite
enumeration in (NAR.15.2) is an effective expression, with no claim about
physical running time, working space or arithmetic width. $\square$

**Theorem 15.3 (the ordered converse and the directed boundary).** For every
$q\ge2$ and $H=q-1$, the following are equivalent:

1. $\mathcal M$ is $q$-wise intersecting.
2. There is a map $f:A_H\to\{0,\ldots,H\}$ that is strictly increasing on
   every $\to_+$ edge.
3. There is such a map that is strictly increasing on every $\to_<$ edge.

When the intersection condition fails, the failure supplies a directed
walk of length $q$ (and, after periodic repetition, a closed directed walk)
in $\to_+$. A directed cycle or a long directed walk alone is not a lower
bound on the chromatic number of the undirected native conflict graph.

**Proof.** The implication 1 to 3 is Theorem 15.2, and 3 to 2 follows from
$\to_+\subseteq\to_<$. For the converse, choose $t\le q$ menu members
$S_1,\ldots,S_t$ with empty intersection and pad the list by repetition to
$R_1,\ldots,R_q$. Define $x^0=0$ and, for $1\le k\le q$,

$$
x^k_i=\max\{r\in\{0,\ldots,k\}:i\in R_{k-r+1},\ldots,R_k\},
\tag{NAR.15.5}
$$

where the empty run has length zero. If $i\in R_k$, then
$x^k_i=x^{k-1}_i+1$; otherwise it is reset to zero. No coordinate has a run
of length $q$, because the padded $q$-fold intersection is empty, so every
$x^k$ lies in $A_H$. Consequently
$x^0\to_+x^1\to_+\cdots\to_+x^q$ is a $q$-edge walk. A strictly increasing
map into $q$ ordered values cannot exist. Repeat the padded list periodically.
Every coordinate is reset at least once per period. After the first period,
its terminal consecutive-membership run therefore depends only on the
periodic region list, so $x^{2q}=x^q$. All run lengths are at most $q-1$,
and the next period gives a closed directed walk in $A_H$. Extracting a
simple cycle is legitimate, but no chromatic conclusion follows merely
from its existence.
$\square$

**Theorem 15.4 (missing-region replication preserves native conflicts).**
For $t\ge2$, let $F_{H,t}$ have vertex set $\{0,\ldots,H\}^{t}$, with an
edge between distinct $x,y$ when for some $j\in\{1,\ldots,t\}$ and some
$d\ne0$,

$$
x_h-y_h=d\qquad(h\ne j).
\tag{NAR.15.6}
$$

The difference at the exceptional coordinate $j$ is unrestricted; it may
also equal $d$. If nonempty $S_1,\ldots,S_t\in\mathcal M$ have empty
intersection, choose $g:I\to\{1,\ldots,t\}$ with $i\notin S_{g(i)}$ and put

$$
\phi(x)_i=x_{g(i)}.
\tag{NAR.15.7}
$$

Then every edge of $F_{H,t}$ maps to a native conflict edge. The map need not
be injective, and its image need not be induced. In particular,
$\chi(F_{H,t})\le N_H(\mathcal M)$.

**Proof.** Empty intersection ensures a missing member for every $i$, so
$g$ exists. If (NAR.15.6) is witnessed outside abstract coordinate $j$, then
for every $i\in S_j$ one has $g(i)\ne j$, hence (NAR.15.7) has the same
nonzero difference $d$ throughout $S_j$. Since $S_j$ is nonempty, at least
one actual coordinate changes: no required edge collapses to a single
vertex. Thus $\phi$ is a graph homomorphism. Pulling back any proper native
code gives a proper code on $F_{H,t}$, proving the displayed inequality.

The actual image sources are $X_{\phi(x)}$ from (NAR.14.1), with every
original offset $iq$ retained and every age outside $I$ fixed at zero. In
each image history the hidden slot exponents still lie in disjoint intervals
$[iq+\ell,iq+H+\ell]$. All depth-$D$ slots are reached and the full hidden
partition is discrete. For an image edge with difference $d$ on $S_j$, take

$$
\ell=\lambda_0+\max(0,-d),\qquad
\ell'=\lambda_0+\max(0,d).
$$

These are unequal allowed lags and give
$\phi(x)_i+\ell=\phi(y)_i+\ell'$ throughout $S_j$. By (NAR.14.3) the two
complete later rows agree, including the literal exterior, labels, brackets,
reached/absent guards and all within-row hidden equality and disequality.
Each history continues its own fixed initial source under pure $\rho$;
there is no splicing of histories. Taking $\lambda_0=1$ also supplies
strictly positive witnesses for the nonnegative-lag convention. Initial
acquisition and export remain those of (NAR.14.2), and (NAR.14.6) supplies
every image age to the encoder. This is a whole-row lag obstruction under
both conventions, with no new acquisition or source-reconstruction premise.
$\square$

**Theorem 15.5 (the uniform arbitrary-color clique-chain obstruction).**
For every $q\ge2$ and $2\le t\le q$, the graph $F_{q-1,t}$ contains a
$q+(q-1)(t-1)$-vertex subgraph that cannot be colored by $q$ arbitrary
colors. Consequently $\chi(F_{q-1,t})\ge q+1$.

**Proof.** Use the following one-spare-color invariant. Let $\mathcal C$ be
any set of $q$ colors, and let $(p_u)_{0\le u\le q-2}$ and
$(r_u)_{0\le u\le q-2}$ be two injective lists in $\mathcal C$. If
$p_u\ne r_v$ whenever $u\ne v$, then the lists differ at at most one
matching position. Indeed, the $p$-list omits exactly one color $z$. At a
changed position $u$, the color $r_u$ differs from $p_u$ by the change and
from every $p_v$ with $v\ne u$ by the cross-index constraints. Hence
$r_u=z$. Two changed positions would repeat $z$ in the injective $r$-list.
For $q=2$ the lists each have one position, so the conclusion also holds,
even though the cross-index constraints are vacuous. This argument uses
only equality and cardinality, without an order on $\mathcal C$.

The certificate vertices are

$$
\begin{aligned}
C_c&=(c,\ldots,c),&&0\le c\le q-1,\\
V_{u,j}&=(\underbrace{u+1,\ldots,u+1}_{j},
          \underbrace{u,\ldots,u}_{t-j}),
 &&0\le u\le q-2,\quad1\le j\le t-1.
\end{aligned}
\tag{NAR.15.8}
$$

Every coordinate is in $\{0,\ldots,q-1\}$. The constants are distinct, and
each nonconstant vertex determines its two values $u,u+1$ and its initial
run length $j$. Thus the displayed count is exact. The subgraph uses the
following edges, all witnessed directly by (NAR.15.6).

The constants form $K_q$, since $C_c-C_{c'}$ has the same nonzero
difference $c-c'$ everywhere when $c\ne c'$. For each fixed $j$, the column
$\{V_{u,j}:0\le u\le q-2\}$ forms $K_{q-1}$, because
$V_{u,j}-V_{v,j}$ is everywhere the nonzero difference $u-v$ when
$u\ne v$. Between consecutive columns, for $u\ne v$,

$$
(V_{u,j}-V_{v,j+1})_h=
\begin{cases}
u-v-1,&h=j+1,\\
u-v,&h\ne j+1.
\end{cases}
\tag{NAR.15.9}
$$

The common displacement $u-v$ is nonzero. Zero at the exceptional
coordinate is permitted, so these are legal edges for every
$1\le j\le t-2$. Finally, $V_{u,1}$ is adjacent to every $C_c$ with
$c\ne u$: outside coordinate $1$ the difference is the nonzero $u-c$.
Likewise $V_{u,t-1}$ is adjacent to every $C_c$ with $c\ne u+1$, using
exceptional coordinate $t$ and nonzero displacement $u+1-c$. These are all
the edge families needed; any additional edges of $F_{q-1,t}$ may remain.

Suppose a proper coloring by at most $q$ colors exists. The constant clique
uses all $q$ colors, so name the color of $C_c$ by $c$. This is a renaming
of an arbitrary palette, without any inequality requirement on labels.
The first-column endpoint edges force $V_{u,1}$ to have color $u$; the
last-column endpoint edges force $V_{u,t-1}$ to have color $u+1$.
Each column is an injective $(q-1)$-list of colors. Equation (NAR.15.9)
imposes all unequal-index cross exclusions on successive lists. By the
one-spare invariant at most one matching position can change across each
transition. Every one of the $q-1$ positions must change between its first
and last colors. Therefore, when $t\ge3$,

$$
q-1\le\sum_{j=1}^{t-2}
 \#\{u:\operatorname{col}(V_{u,j})\ne
              \operatorname{col}(V_{u,j+1})\}
\le t-2\le q-2,
\tag{NAR.15.10}
$$

which is impossible. At $t=2$ the first and last columns coincide, and
their two endpoint requirements already force the same vertex to have the
distinct colors $u$ and $u+1$. In particular, $q=t=2$ gives the triangle
$00,11,10$. No transition is needed in this boundary case. This proves the
obstruction for every stated parameter. $\square$

**Corollary 15.6 (the universal minimum-alphabet classification).** For
all $H\ge1$, with $q=H+1$,

$$
N_H(\mathcal M)=q
\quad\Longleftrightarrow\quad
\mathcal M\text{ is }q\text{-wise intersecting}.
\tag{NAR.15.11}
$$

If the intersection condition fails, $N_H(\mathcal M)\ge q+1$. This
necessity quantifies all retained encoders, without requiring their labels
to increase along either oriented relation of Assumption 15.1.

**Proof.** For every nonempty menu the constant age vectors
$C_0,\ldots,C_H$ form a native $q$-clique: each pair has a nonzero constant
displacement on any selected nonempty region. Thus $N_H(\mathcal M)\ge q$.
Under $q$-wise intersection Theorem 15.2 supplies exactly $q$ labels, with
its acquired-row factor and effective decoder.

If the condition fails, take $t\le q$ members with empty intersection.
Nonemptiness of every member ensures $t\ge2$. Theorem 15.4 maps
$F_{q-1,t}$ into the actual native conflict graph without collapsing any
edge, and Theorem 15.5 forbids a $q$-coloring of its certificate. Any
sufficient retained code must separate all those image edges by Reuse 14.2.
Composing it with the replication map would otherwise color the
certificate with $q$ colors. The unequal legal lags and equal complete
later rows in Theorem 15.4 are exactly the native witnesses for this
contradiction. Conversely, the proper rank code is acquired before the
future choice and decodes with no extra input by (NAR.15.3). Both arguments
apply to both lag conventions.

Theorem 15.3 remains the separate ordered-code characterization; its cycle
alone is not the arbitrary-color proof. The bound $q+1$ here does not
replace a stronger bound for a particular menu. In particular, disjoint
regions still force $q^2$ labels by Theorem 14.5, and the binary price can
never be three by Theorem 14.3. The exact binary half-boundary and stronger
binary diameter bounds in section 13 retain their stated force. $\square$

**Theorem 15.7 (all $k$-subsets and the exact minimum-alphabet threshold).**
Let $I$ have $r\ge1$ positions, let $1\le k\le r$, and let
$\mathcal M_{r,k}$ consist of every $k$-subset of $I$. For every $q\ge2$,

$$
\mathcal M_{r,k}\text{ is }q\text{-wise}
\quad\Longleftrightarrow\quad
q(r-k)<r.
\tag{NAR.15.12}
$$

Consequently, for $H\ge1$ and $q=H+1$, $N_H(r,k)=q$ exactly when this
strict inequality holds; otherwise $N_H(r,k)\ge q+1$. For $H=0$, the
single age profile has $N_0(\mathcal M)=1$ for every nonempty menu in
Assumption 14.1, independently of this threshold.

**Proof.** The intersection of $q$ members is empty exactly when their
complements, each of size $r-k$, cover $I$. If $q(r-k)<r$, their total
capacity cannot cover all $r$ positions, and the same is true for fewer
members. If $q(r-k)\ge r$ and $r-k>0$, distribute the positions among
$q$ blocks of size at most $r-k$, then extend each block to size $r-k$
within $I$. These extended blocks cover $I$. Their complements are menu
members with empty intersection; repetitions can be removed, leaving at
most $q$ members. When $k=r$, the complements are empty and the strict
inequality holds. Formula (NAR.15.11) now supplies the native equivalence
for every $q\ge2$.

At $H=0$ there is just $a=0$. Every nonempty selected region displays
normalized values $z_i=\ell$, so a single retained value and any public
$i\in S$ recover the lag under either convention. This is also the
zero-age case of Theorem 14.5. $\square$

**Proposition 15.8 (a direct ternary rank and median collisions).** For
$H=2$, $r=4$ and $k=3$, the direct encoder supplied by (NAR.15.2) is

$$
E(a)=
\begin{cases}
0,&\#\{i:a_i=0\}\ge2,\\
2,&\#\{i:a_i=2\}\ge2,\\
1,&\text{otherwise}.
\end{cases}
\tag{NAR.15.13}
$$

Neither the lower nor the upper median is a sufficient retained code for
this native menu, although (NAR.15.13) is a sufficient three-label code.

**Proof.** The first branch must be tested first. Rank at least one means that some
three-subset is entirely positive, equivalently at most one zero. Rank at
least two further requires the two witnessing three-subsets to intersect
only at positions of age two; their intersection has at least two positions.
Conversely, if at most one age is zero and at least two ages are two, choose
a positive three-subset containing two such positions and a second
three-subset whose intersection with it is exactly those two. These are the
two suffix conditions in (NAR.15.2). This proves (NAR.15.13), and Theorem
15.2 supplies its native decoder.

The lower median does not supply this code: $a=(1,0,1,1)$ and
$b=(0,1,2,2)$ both have lower median $1$, whereas (NAR.15.13) gives $1$ and
$2$. The upper median also fails: $a=(1,0,0,1)$ and
$b=(0,1,1,2)$ both have upper median $1$, whereas their codes are $0$ and
$1$. In both examples $b-a=(-1,1,1,1)$, so the displacement is $1$ throughout
the selected triple $S=\{1,2,3\}$. With original offsets $0,3,6,9$, the two
actual histories at
lags $2$ and $1$ have equal normalized selected values and therefore equal
complete later rows by (NAR.14.3), including their hidden partition. These
are native collisions, not merely equal summaries of four numbers. The
failure is a failure of the median rules, while the three-label encoder
remains valid. $\square$

**Proposition 15.9 (a six-region, thirty-one-source native consumer).**
At $D=3$ write $W_3=\{w_0,\ldots,w_7\}$ in the original lexicographic
order $LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR$. Take
$P=\{w_6,w_7\}$, $I=\{0,\ldots,5\}$, $H=5$ and $q=6$. The actual
source family is

$$
X_a=\mathcal B_3[T_{a_0},T_{6+a_1},T_{12+a_2},T_{18+a_3},
                 T_{24+a_4},T_{30+a_5},T_{36},T_{42}],
\qquad a\in\{0,\ldots,5\}^{6}.
\tag{NAR.15.14}
$$

Let $\mathcal M=\{S_h:0\le h\le5\}$, where $S_h=I\setminus\{h\}$,
so $Q_{S_h}=\{w_h,w_6,w_7\}$. The $q=t=6$ certificate of (NAR.15.8)
gives $31$ distinct actual sources and $195$ distinct named native conflict
edges. Under either lag convention,

$$
7\le N_5(6,5)\le36.
\tag{NAR.15.15}
$$

No exact alphabet size beyond these bounds is asserted.

**Proof.** The six co-singletons are $5$-wise intersecting, since any at
most five exclude at most five positions, but their sixfold intersection
is empty. Index abstract coordinates by $1,\ldots,6$ and let abstract
region $i+1$ denote $S_i$. The only member missing original position $i$
is $S_i$, so the replication choice is $g(i)=i+1$ and
$\phi(x)_i=x_{i+1}$. This identifies the six abstract ages with the six
original exposed ages. The $6+5\cdot5=31$ distinct profiles in (NAR.15.8) therefore
give $31$ distinct sources in (NAR.15.14), with the two other ages fixed at
zero and the original offsets $0,6,12,18,24,30,36,42$ unchanged.

The named edges consist of $\binom62=15$ constant-clique edges,
$5\binom52=50$ within-column edges, $4\cdot5\cdot4=80$
unequal-index edges between consecutive columns, and $2\cdot5\cdot5=50$
endpoint-to-constant edges. These four families are disjoint: they join,
respectively, two constants, two vertices in one column, two vertices in
successive columns, or a constant and a vertex in one of the two distinct
endpoint columns. Thus their total is $195$. The identities in Theorem
15.5 supply a nonzero displacement on the co-singleton outside the
exceptional coordinate for each edge.

Every depth-three slot is reached in each history. At every lag the eight
exponent intervals of length at most five are disjoint. Therefore all three
hidden values at $Q_{S_h}$ are pairwise unequal, and the complete hidden
partition is discrete, including the two fixed original slots. Applying
Theorem 15.4's lags gives equal complete later rows on each named edge;
with $\lambda_0=1$ those witnesses have $1\le\ell,\ell'\le6$ and work
under either lag convention. Initial acquisition displays the six variable
subtrees and computes their ages by (NAR.14.6). Theorem 15.5 rules out
six retained labels for this genuine future-menu task, proving the lower
bound.

For the upper bound retain the acquired ages at two distinct public
exposed positions, for example $(a_0,a_1)$. Every five-position region
contains at least one of them; use its later normalized value minus its
retained age. All $6^2=36$ tuples occur, so this is a proper $36$-label
encoder, also the transversal bound of Theorem 14.5. Its export precedes
the future region choice. Thus (NAR.15.15) follows.

The fixed-width representation price satisfies only
$3\le\lceil\log_2N_5(6,5)\rceil\le6$. Increasing the forced alphabet
from six to at least seven does not force a fourth bit, since both six and
seven labels fit in three bits. Label and fixed-width bit counts exclude
acquisition, source storage, decoder controls, parsing, arithmetic width,
workspace, transmission and physical time. $\square$

**Mathematical citation 15.10 (correspondence and boundaries).** The native
clock, literal-row and full hidden-partition suppliers are
right_clock_iterate in
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean),
canonicalRow_record_iff in
[ActualCutPartitionDecoder](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean),
and legal_values_row/rowFiberEquiv in
[NativeCutFibers](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean).
Sections 13 and 14 supply the separated-age family, acquired-row factor,
complete-row collision and finite decoder reused above. Witsenhausen's
*The zero-error side information problem and chromatic numbers* (1976), and
Charpenay--Le Treust--Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*](https://arxiv.org/html/2211.03649v2), are the mature
zero-error coding correspondence; their stochastic, asymptotic or unrestricted
side-information hypotheses are not imported.

The longest-path coloring mechanism is the classical direction of Roy,
[*Nombre chromatique et plus longs chemins d'un graphe* (1967),
Theorems 1--2](https://www.numdam.org/item/M2AN_1967__1_5_129_0.pdf), with the
finite directed formulation also recorded by Fujita--Kitaev--Sato--Tong,
arXiv:2102.08432, Theorems 3--4. The use here is the explicit native rank
(NAR.15.2), not a claim that one directed cycle lower-bounds an arbitrary
chromatic number. Freixas--Kurz, arXiv:1711.06611, supplies the Nakamura
empty-intersection parameter analogy for simple games; it does not identify
the native age alphabet with their alternatives.

For the clique-chain correspondence use Briceño--Bulatov--Dalmau--Larose,
[*Dismantlability, connectedness, and mixing in relational structures*,
arXiv:1901.04398v3, §2.4 and Lemma 2.9](https://arxiv.org/html/1901.04398v3).
Their reflexive recoloring graph $C(G,K)$ joins two homomorphisms differing
at at most one source vertex. Their link graph $L(G,K)$ instead imposes
all mixed-tuple constraints, and Lemma 2.9 identifies homomorphisms from a
link product $\mathbb L_\ell\times G$ with length-$\ell$ walks in $L(G,K)$.
For $t\ge3$ set $G=K_{q-1}$, $K=K_q$, $\ell=t-2$, and map source vertex
$u$ at link position $j-1$ to the color of $V_{u,j}$. Within-column
injectivity is exactly the homomorphism condition into loopless $K_q$;
the mixed constraints are exactly the unequal-index exclusions in
(NAR.15.9). The one-spare invariant in Theorem 15.5 proves directly, for
these particular complete graphs, that each such link step changes at most
one position. The two forced endpoint maps differ at every one of the
$q-1$ positions, so no walk of the stated length exists. At $t=2$ the
endpoint contradiction is separate; no length-zero version of the cited
lemma is assumed. No mixing, dismantlability, connectivity or general
recoloring-diameter theorem is used.

The native minimum-alphabet classification, direct rank formula,
missing-region transfer and six-region consumer are repo-derived ordinary
deductions from the stated suppliers and explicit proofs. The literature
above supplies the coding, rank and link/recoloring correspondences as
intermediate methods, not an asserted published native memory theorem.
There is no worldwide novelty or Lean/kernel-verification claim.

These statements concern the entire stated finite independent-age family,
the public finite nonempty future menu, a code exported before its member
and the lag are chosen, and exactly one complete later row. They recover
lag without asserting source reconstruction, all-source coverage, acquisition
legality, a physical memory or time optimum, or an acquisition/authentication
optimum. Rank paths compare alternative profiles and are not actual
$\rho$ histories. The minimal-$q$ regime is classified for every $q$.
The classification does not determine the price for a general menu above
$q$; in particular, the exact value of $N_5(6,5)$ within (NAR.15.15)
remains undetermined. The exact prices and sharper bounds of sections 13
and 14 retain their stated scope.

## 追加锚（本行以下为增补区）

## 16. Retained origin reference and paid stationary current-source recovery

**Assumption 16.1 (a current port after acquisition, export and discard).**
Use the actual finite ordered trees, homomorphic $\rho$, four-valued
literal Read and complete rows of Definitions 1.1--1.2. Fix public
integers $D,H\ge0$, and write

$$
\begin{aligned}
P&=\varnothing,&r&=2^D,&q&=H+1,\\
W_D&=(w_0,\ldots,w_{r-1}),&I&=\{0,\ldots,r-1\},\\
T_n&=\rho^n\alpha,&
X_a&=\mathcal B_D[(T_{jq+a_j})_{j\in I}],&
a&\in\{0,\ldots,H\}^{I}.
\end{aligned}
\tag{NAR.16.1}
$$

The original words are in lexicographic order, with $w_0=L^D$;
$\mathcal B_D$ is the complete ordered depth-$D$ skeleton. All original
slots have independent variable ages, and their offsets remain $jq$.
Let $\mathcal M$ be any nonempty public family of nonempty subsets of
$I$. For a later selected $S\in\mathcal M$ put
$Q_S=W_D\setminus\{w_i:i\in S\}$. Fix $\lambda_0\in\{0,1\}$ and
allow every integer lag $\ell\ge\lambda_0$. The stationary current tree
and its supplied later row are

$$
Y(a,\ell)=\rho^\ell X_a
 =\mathcal B_D[(T_{jq+a_j+\ell})_{j\in I}],
\qquad V_S(a,\ell)=R_{Q_S}(Y(a,\ell)).
\tag{NAR.16.2}
$$

The encoder computes one code solely from the genuinely acquired
initial $R_{\varnothing}(X_a)$, before both $S$ and $\ell$ are chosen.
It exports that code and discards the initial row and every other
source-bearing field. Write its induced finite age function as $e(a)$.
All surviving source-bearing distinctions count as code: retained IDs,
clock values, epochs, logs, sizes, readable pointers, allocation
choices, archives and source-dependent controller states have no
separate uncharged channel. Public parameters and installed tables
common to all sources are not acquired facts about the chosen source.

The decoder starts with $S$, $e(a)$ and the full acquired $V_S(a,\ell)$.
This includes the literal exterior, every label and bracket, all reached
or absent-cut guards, and all within-row hidden equalities and
disequalities. It contains no hidden subtree values or cross-row links.
In addition, the decoder may pay for a fresh native Read at any finite
literal original-root address $p\in\{L,R\}^{<\omega}$ of this same
stationary CURRENT $Y(a,\ell)$. The replies are
$\mathsf{absent},\alpha,\beta,\mathsf{branch}$. A request returns one
constructor reply, not a subtree or a numerical age. There is no old
source reread, epoch advice, free equality or age oracle, reroot service,
or native update during the later capture or decoder queries.

A deterministic adaptive controller chooses its next finite address or
halts from the supplied entry and its acquired reply history. Correct
finite recovery means one encoder and controller satisfy

$$
\forall a\ \forall S\in\mathcal M\ \forall\ell\ge\lambda_0:
\quad\mathsf{Dec}^{\operatorname{Read}_{Y(a,\ell)}}
       (S,e(a),V_S(a,\ell))\text{ halts with output }\ell.
\tag{NAR.16.3}
$$

Each actual invocation is one raw call, including an absent reply, a
repeated address or a visible-address reread. Local evaluation of an
already acquired literal exterior is not a fresh source call. It still
has parsing and arithmetic costs. The literal word $R^s$ has $s$ actual
letters; an integer specifying $s$ is not a compressed native request.

Acquisition, truthful export/discard, stationary capture, permissions
and same-source, same-root, pure-$\rho$ continuation are premises.
They grant neither a value of $\ell$ nor authentication by the output.
Labels, fixed-width bits, fresh calls, literal address lengths and their
sum, acquisition, row storage, parsing, arithmetic, address production,
controller workspace and lag-output size are separate resources.
This explicitly enlarged current-access contract does not alter the
zero-extra-read contracts of §§13--14.

**Reuse 16.2 (the acquired factors and the complete later-record supplier).**
On (NAR.16.1), the right clock $c$ supplied by `right_clock_iterate`
satisfies $c(T_n)=n$. The initial acquired literal row therefore computes

$$
a_j=c(X_a|_{w_j})-jq,\qquad j\in I.
\tag{NAR.16.4}
$$

Thus any finite function $e(a)$ can be encoded from the initial row,
without access to an unacquired age profile. For every displayed slot,
local parsing of the later acquired literal tree gives

$$
z_i=c(Y(a,\ell)|_{w_i})-iq=\ell+a_i,\qquad i\in S.
\tag{NAR.16.5}
$$

Reuse Theorem 13.3, or (NAR.14.3), separately for each $S$:

$$
V_S(a,\ell)=V_S(b,\ell')
\quad\Longleftrightarrow\quad
 a_i+\ell=b_i+\ell'\quad(i\in S).
\tag{NAR.16.6}
$$

This is equality of the whole row. Every original depth-$D$ slot is
reached, including leaf fillings. Within either history the exponent
bands $[jq+\ell,jq+H+\ell]$ are disjoint at different $j$, so every
hidden partition is discrete. Equality of displayed literals fixes the
entire exterior, all guards and every hidden comparison. A scalar
collision without this complete-record supplier would be insufficient.
The inherited zero-read conflict relation is

$$
a\sim_{\mathcal M}b
\quad\Longleftrightarrow\quad
\exists S\in\mathcal M\ \exists d\ne0:\quad a_i-b_i=d\quad(i\in S).
\tag{NAR.16.7}
$$

By the existing finite candidate decoder in §13.3 and Reuse 14.2,
zero-extra-read recovery for $e$ is equivalent to separating every edge
of (NAR.16.7). This graph principle is reused; the current-port and
address conclusions below require additional native arguments.

**Theorem 16.3 (whole-current equivalence and irrecoverable common origin).**
Two histories in Assumption 16.1 have identical replies at every finite
current address exactly when

$$
Y(a,\ell)=Y(b,\ell')
\quad\Longleftrightarrow\quad
 a_j+\ell=b_j+\ell'\quad(j\in I).
\tag{NAR.16.8}
$$

Unequal-lag whole-current collisions are consequently exactly common
nonzero translations $a-b=(\ell'-\ell)\mathbf1$ of all initial ages.
Even arbitrary input-dependent finite adaptive all-address querying
requires at least $q$ attained retained labels in (NAR.16.3).

**Proof.** Complete four-valued Read separates finite ordered trees.
At the root it separates $\alpha$, $\beta$ and branch. For two branches
with unequal children, descend to an unequal child and continue by
structural induction. The distinguishing child word, prefixed by $L$
or $R$, is a finite original-root word. Equal trees have equal replies,
including all absent-address replies. Hence all-address equality is
literal tree equality, rather than equality of a coarser summary.

At each reached original $w_j$, equality of the whole current trees
forces equality of $T_{jq+a_j+\ell}$ and $T_{jq+b_j+\ell'}$.
Applying $c(T_n)=n$ gives the right side of (NAR.16.8). Conversely those
exponent equalities give the same filling in every slot of the same
ordered skeleton, proving equality of the whole current trees.

For $t=0,\ldots,H$, let $a^{(t)}=t\mathbf1$ and choose the positive
lag $\ell_t=q-t$. Every one of these $q$ histories has the same WHOLE
current tree

$$
Y(a^{(t)},\ell_t)=\mathcal B_D[(T_{jq+q})_{j\in I}].
\tag{NAR.16.9}
$$

Fix any one $S\in\mathcal M$. Its full later row is also identical for
all these histories. If two initial profiles received one code, the two
decoders would have exactly the same entry. Equal entry and equal past
reply history determine equal next addresses or equal halt decisions.
The identical stationary current tree gives equal replies at the chosen
addresses. Induction therefore gives equal adaptive histories and
outputs, whenever they halt. Finite correctness would require different
outputs $q-t$, a contradiction. The $q$ codes must be distinct.

More generally, any nonzero common translation can be realized at
positive lags: if $a-b=d\mathbf1$, take
$\ell=\max(1,1-d)$ and $\ell'=\ell+d$. The same induction applies.
These compare different histories at different lags. At a fixed $\ell$,
(NAR.16.8) instead forces $a=b$; no fixed-epoch noninjectivity of
$\rho$ is asserted. $\square$

**Theorem 16.4 (an acquired first-slot reference attains the exact label price).**
Retain only

$$
e_0(a)=a_0=c(X_a|_{w_0}),\qquad w_0=L^D.
\tag{NAR.16.10}
$$

This code has exactly $q$ attained labels and permits recovery with at
most $\lfloor\log_2q\rfloor$ fresh raw calls, uniformly in $a,S,\ell$.
It uses zero fresh calls whenever $0\in S$. Thus the exact minimum
retained alphabet under (NAR.16.3) is $q$, and its fixed-width binary
representation price is $\lceil\log_2q\rceil$ bits. The stated raw-call
bound is sufficient, without a general optimal-call assertion.

**Proof, the acquired interval.** Formula (NAR.16.4) computes the code
from the initial literal row; the public reference address does not
make its initial age public. If $0\in S$, return $z_0-e_0(a)$ using the
already acquired exterior and no new Read. Otherwise choose the public
$i=\min S$, parse $z=z_i$, and write $c_0=e_0(a)$. Since
$z=\ell+a_i$, $0\le a_i\le H$ and $\ell\ge\lambda_0$, the unknown
first-slot exponent $n_0=\ell+c_0$ lies in the finite integer interval

$$
[A,B]=[c_0+\max(\lambda_0,z-H),\ c_0+z],
\qquad 1\le B-A+1\le q.
\tag{NAR.16.11}
$$

It is nonempty on every promised input because it contains $n_0$.
The upper size bound follows from $\max(\lambda_0,z-H)\ge z-H$.

**Proof, one actual Read and interval restriction.** For every reached
slot $w_j$ with filling $T_n$, the supplied `right_clock_readout`
applied to that subtree gives the following single-address experiment:

$$
\begin{array}{c|cccc}
\operatorname{Read}_{Y}(w_jR^s)
 &\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\ \hline
\text{condition on }n
 &n<2s&n=2s&n=2s+1&n\ge2s+2.
\end{array}
\tag{NAR.16.12}
$$

Read follows the reached public prefix $w_j$ before its literal right
suffix. The upper reply interval includes $2s+2$. The four answers are
native constructors and absence; the decoder is never given $n$ by an
oracle. Here $T_0=\alpha$, $T_1=\beta$ and
$T_{n+2}=\langle T_{n+1},T_n\rangle$ are the underlying recurrence.

For a current integer candidate interval $[L,U]$ of size $K\ge2$, put

$$
m=L+\lfloor K/2\rfloor,\qquad
 t=2\lfloor m/2\rfloor,\qquad s=t/2.
\tag{NAR.16.13}
$$

These are nonnegative integers, and $t$ is either $m$ or $m-1$.
Submit the one literal word $w_jR^s$. Intersect $[L,U]$ with the reply
block from (NAR.16.12): respectively

$$
(-\infty,t-1],\qquad\{t\},\qquad\{t+1\},\qquad[t+2,\infty).
\tag{NAR.16.14}
$$

Every nonempty block is an integer interval. The lower block has at
most $\lfloor K/2\rfloor$ candidates. For the upper block, writing
$f=\lfloor K/2\rfloor$, the worst case $t=L+f-1$ gives at most
$K-f-1\le f$ candidates. The two singleton blocks have size one,
which is also at most $f$. Empty blocks cannot be the actual reply.
Thus every call preserves the actual exponent and reduces the candidate
count to at most $\lfloor K/2\rfloor$. A singleton is output locally,
without an additional confirmation Read.

Induction on $K$ gives at most $\lfloor\log_2K\rfloor$ calls:
for $K=1$ the count is zero, and for $K\ge2$ it is at most
$1+\lfloor\log_2\lfloor K/2\rfloor\rfloor
 =\lfloor\log_2K\rfloor$. Apply this actual interval procedure at
$j=0$ to (NAR.16.11), and return the recovered $n_0-c_0=\ell$.
All query choices use only code, acquired later row and previous replies.
Every $c_0\in\{0,\ldots,H\}$ occurs, for example on a constant profile.
Theorem 16.3 supplies the matching retained-label lower bound.
The native halving calculation establishes the claimed service bound;
it does not authorize arbitrary subset tests. $\square$

**Theorem 16.5 (exact feasibility for every fixed encoder).** For a fixed
acquired encoder $e$ on (NAR.16.1), the following are equivalent:

1. It supports finite adaptive current recovery in (NAR.16.3).
2. It separates every pair $a,b$ with $a-b=d\mathbf1$ and $d\ne0$.
3. It supports current recovery with one finite raw-call bound uniform
   over all profiles, menu choices and legal unbounded lags.

When condition 2 holds, a native construction uses at most

$$
C_e(S)=(r-|S|)\lfloor\log_2(2H+1)\rfloor
\tag{NAR.16.15}
$$

fresh calls on every input with that $S$. Its bound over the menu is
$\max_{S\in\mathcal M}C_e(S)\le(r-1)\lfloor\log_2(2H+1)\rfloor$.
This is an attained upper bound for the specified encoder, not its
minimum call count.

**Proof.** Condition 3 implies condition 1. If condition 2 fails,
Theorem 16.3 realizes a same-code pair with the identical whole current
tree at positive distinct lags, refuting condition 1.

For condition 2 implying condition 3, choose any public $i\in S$ and
parse $z=z_i$. Set $A_\ell=\max(\lambda_0,z-H)$ and $B_\ell=z$.
For every hidden slot $j\notin S$, its unknown exponent
$n_j=jq+a_j+\ell$ lies in

$$
[jq+A_\ell,\ jq+B_\ell+H],
\qquad B_\ell+H-A_\ell+1\le2H+1.
\tag{NAR.16.16}
$$

Use exactly the native interval procedure (NAR.16.12)--(NAR.16.14)
at $w_jR^s$ for each hidden slot. Visible $n_j$ are already parsed
from their acquired literals. This obtains the whole normalized vector
$x_j=n_j-jq$ with the fresh-call bound (NAR.16.15). It acquires clock
values through finite native replies, without traversing whole trees.

Enumerate the finite age cube using the fixed source-independent table
for $e$. For each $b$ with the received code, let $h=x_i-b_i$ and keep
it exactly when $h\ge\lambda_0$ and $x_j=b_j+h$ for every $j\in I$.
The actual $a$ with $h=\ell$ survives. If two survivors $b,b'$ gave
different $h,h'$, then $b-b'=(h'-h)\mathbf1$ would be a same-code
nonzero common translation, contrary to condition 2. Return their unique
common lag; uniqueness of the initial profile is unnecessary.
This finite enumeration and interval search terminate on promised inputs.
The intervals contain a uniformly bounded number of integers even when
their endpoints, tree sizes and query words grow with $\ell$.
Pointwise finite full-tree traversal alone would not have supplied this
uniform raw-call conclusion. $\square$

**Theorem 16.6 (uniform literal-address caps recover the zero-read obligation).**
Fix any acquired encoder $e$. There exists a correct finite current
recovery protocol and a finite $B$ such that every fresh query satisfies
$|p|\le B$ on every promised input if and only if $e$ already separates
every edge of the zero-read menu relation (NAR.16.7). No uniform bound
on the number of those capped calls is needed for the necessity.

More precisely, suppose $e(a)=e(b)$ and a conflict is witnessed by
$S,d$ with $a_i-b_i=d\ne0$ for $i\in S$. Choose positive baseline lags
$\ell_0,\ell'_0$ with $\ell'_0-\ell_0=d$, and define

$$
\mu=\min_{j\in I}\{jq+a_j+\ell_0,\ jq+b_j+\ell'_0\},
\qquad M_K=K+\mu.
\tag{NAR.16.17}
$$

For every integer $K\ge0$ with $M_K\ge2$, any correct recovery protocol
for $e$, if one exists, must on these shifted histories issue a
distinguishing native query of length at least

$$
D+\left\lfloor\frac{K+\mu}{2}\right\rfloor.
\tag{NAR.16.18}
$$

This gives a linear address witness even when the encoder is otherwise
feasible under Theorem 16.5. If the pair also collides as a whole current
tree, recovery is impossible outright by Theorem 16.3.

**Proof, common shifts preserve the whole later entry.** Choose
$\ell_0=\max(1,1-d)$ and $\ell'_0=\ell_0+d$. At every common added
$K$, (NAR.16.6) gives

$$
V_S(a,\ell_0+K)=V_S(b,\ell'_0+K).
\tag{NAR.16.19}
$$

The proof includes the entire exterior and hidden partition, because
separated original offset bands remain disjoint after the shift.
The two codes and public inputs agree too, whereas required lag outputs
remain distinct. The common later row can vary with $K$; equality is
between the two histories at each $K$, not between different shifts.

**Proof, shallow-prefix stabilization.** The least leaf depth $h(n)$ of
$T_n$ satisfies $h(0)=h(1)=0$ and, from the recurrence,
$h(n+2)=1+\min(h(n+1),h(n))$. Induction gives $h(n)=\lfloor n/2\rfloor$.
Every word shorter than that least leaf depth reaches a branch: complete
binary branching ensures the word is reached, and minimality excludes
a leaf. In the whole tree (NAR.16.2), the complete skeleton contributes
$D$ edges before a slot. Since all slot exponents in both shifted trees
are at least $M_K$, every finite word with

$$
|p|<D+\lfloor M_K/2\rfloor
\tag{NAR.16.20}
$$

has reply $\mathsf{branch}$ on both histories. Equivalently the common
all-branch prefix includes depths through
$D+\lfloor(M_K-2)/2\rfloor$. This assertion is about full replies,
not only agreement of address presence. It applies to all words in that
prefix, not only right rays.

**Proof, adaptive induction and the converse.** Until a first differing
reply the decoder histories are identical: equal entries and replies
force equal local computations, next words and halt decisions. Correct
finite recovery of different lags must eventually obtain a differing
reply; otherwise the two halt outputs would agree. By (NAR.16.20) that
first distinguishing word obeys (NAR.16.18). Repeated shallow requests,
arbitrarily many finite capped requests, and unbounded local arithmetic
cannot change the induction.

For any alleged uniform cap $B$, choose $K$ so large that
$D+\lfloor(K+\mu)/2\rfloor>B$. Every allowed request then has the same
branch reply on the two entries, contradicting finite correctness.
Thus a code merging any zero-read edge admits no uniform address cap.
Conversely, if it separates all these edges, Reuse 16.2's finite
zero-read candidate decoder already returns the lag. It makes no
requests and has the vacuous address cap zero. This proves both
directions for every fixed encoder. $\square$

**Proposition 16.7 (explicit retained, raw-call and address coordinates).**
For the first-slot protocol, let $Q=\lfloor\log_2q\rfloor$. On every
promised input its retained and newly queried quantities satisfy

$$
\begin{aligned}
\#\text{ attained retained labels}&=q,\\
\text{fixed-width retained bits}&=\lceil\log_2q\rceil,\\
K_{\mathrm{fresh}}&\le Q,\\
|p|&\le D+\left\lfloor\frac{\ell+2H}{2}\right\rfloor
          &&\text{for every fresh word},\\
\sum_{\mathrm{fresh\ calls}}|p|
 &\le Q\left(D+\left\lfloor\frac{\ell+2H}{2}\right\rfloor\right).
\end{aligned}
\tag{NAR.16.21}
$$

If $0\in S$, both fresh-call quantities and the address-length sum are
zero. For the general feasible-encoder construction of Theorem 16.5,
the analogous per-word and summed-length bounds are

$$
|p|\le D+\left\lfloor\frac{(r-1)q+\ell+2H}{2}\right\rfloor,
\qquad
\sum|p|\le C_e(S)
 \left(D+\left\lfloor\frac{(r-1)q+\ell+2H}{2}\right\rfloor\right).
\tag{NAR.16.22}
$$

These price post-entry literal requests only.

**Proof.** In (NAR.16.13), $t\le L+\lfloor K/2\rfloor\le U$ when
$K\ge2$, so $s\le\lfloor U/2\rfloor$. Every later interval is a
subinterval of the initial one. For the first-slot search its original
upper endpoint $c_0+z=\ell+a_0+a_i$ is at most $\ell+2H$.
The word has $D+s$ literal letters. Multiply its bound by the already
established call bound. For a hidden $j$ in Theorem 16.5 the upper
endpoint is $jq+z+H\le jq+\ell+2H$, and $j\le r-1$, giving
(NAR.16.22). Label attainment and representation follow from Theorem
16.4. No optimum for summed or maximum addresses follows from an upper
bound on this particular construction.

The acquired rows can themselves grow with the lag. Parsing their
literal syntax, computing clocks and interval endpoints, constructing
and transmitting long words, and enumerating compatible profiles have
costs outside the retained-label and raw-call coordinates. The integer
output has unbounded size as $\ell$ ranges without bound; its usual
binary representation has $\lceil\log_2(\ell+1)\rceil$ bits for
$\ell\ge1$, with a separate representation convention at zero.
A public table for a fixed $e$ is common control data, while a
source-dependent pre-discard table choice would count as retained code.
No total or peak memory, running-time, execution, acquisition-cost or
physical-time bound is established by (NAR.16.21)--(NAR.16.22).
$\square$

**Proposition 16.8 (a native two-slot strict saving with a long-address witness).**
Take $D=1,H=1$, so $r=q=2$, and
$\mathcal M=\{\{0\},\{1\}\}$. Zero-extra-read recovery needs exactly
four retained labels, whereas current recovery needs exactly two and
the code $e_0=a_0$ uses at most one fresh Read. For any two-label code
with a correct current decoder, at least one fresh call is necessary in
the worst case; the displayed first-slot protocol attains one.
The retained fixed-width representations cost respectively two bits
with zero fresh reads and one bit with the displayed current protocol.

**Proof.** The four actual initial sources have the form
$X_a=\langle T_{a_0},T_{2+a_1}\rangle$, $a\in\{0,1\}^2$.
Any pair of distinct vectors differs at some singleton position by
$1$ or $-1$, hence conflicts under (NAR.16.7). The zero-read graph is
$K_4$: four distinct labels are necessary, and retaining both ages is
sufficient. Theorems 16.3--16.4 give exactly two current-access labels
and at most $\lfloor\log_22\rfloor=1$ Read. A two-label zero-call
protocol would contradict the just established four-label necessity.

For an explicit cost transfer let

$$
a=(0,0),\qquad b=(0,1),\qquad S=\{1\},\qquad
\ell=N,\quad\ell'=N-1,\qquad N\ge2.
\tag{NAR.16.23}
$$

Both codes $a_0,b_0$ are zero. Both complete later exteriors are
$\langle\square_L,T_{N+2}\rangle$, with the same reached singleton
hidden class and all the same visible absence guards. The current trees
are $\langle T_N,T_{N+2}\rangle$ and
$\langle T_{N-1},T_{N+2}\rangle$. Their hidden subtrees differ.
All words of length less than $1+\lfloor(N-1)/2\rfloor$ reply branch
on both. Thus any correct decoder for this code must issue a
distinguishing word of length at least $1+\lfloor(N-1)/2\rfloor$.
The one-call saving has no lag-uniform literal-address cap. $\square$

**Proposition 16.9 (degenerate cases, alternative memory and a different domain).**
If $H=0$, one label and zero fresh calls suffice. If $D=0$, every
nonempty $S$ contains the only slot and the first-slot protocol makes
zero calls; for arbitrary $D$, the same holds when $S=I$. The exact
$q$-label necessity still holds when $H>0$ in these visible-anchor cases.
All conclusions above apply to positive and nonnegative lag conventions.

The alternative code $e_{\min}(a)=\min_{j\in I}a_j$ is feasible and
has $q$ attained labels. Theorem 16.5's construction followed by

$$
\ell=\min_{j\in I}(n_j-jq)-e_{\min}(a)
\tag{NAR.16.24}
$$

gives a valid protocol with (NAR.16.15)'s sufficient call bound. The
first-slot code has the stronger stated uniform guarantee of Theorem
16.4; neither is asserted to dominate all other resource coordinates.

A proper variable set $I'\subsetneq I$ with one public fixed-age-zero
slot $j_*\notin I'$ is a different source domain. If a nonempty selected
region lies in $I'$ and the same all-address current port is permitted,
a constant retained code suffices with at most $\lfloor\log_2q\rfloor$
fresh calls, irrespective of whether that anchor is displayed.

**Proof.** At $H=0$ every acquired visible $z_i$ is already $\ell$.
At $D=0$ nonempty selection forces $S=\{0\}$, and at $S=I$ the
first-slot clock is displayed. Subtraction uses zero new Reads, while
the identical-whole-current witnesses (NAR.16.9) still force $q$ labels.
Those witnesses have positive lags, so apply to both conventions;
$\lambda_0$ only adjusts the search lower endpoint.

A common translation by $d$ changes the minimum age by $d$.
Thus $e_{\min}$ separates every nonzero common translation and Theorem
16.5 applies without a separate weaker search proof. All its labels are
attained on constant profiles; (NAR.16.24) follows because
$n_j-jq=\ell+a_j$.

For the different domain retain the original offsets, set
$a_{j_*}=0$ publicly, and choose a visible variable slot with
$z=\ell+a_i$. Its current anchor exponent is $j_*q+\ell$, lying in

$$
[j_*q+\max(\lambda_0,z-H),\ j_*q+z].
\tag{NAR.16.25}
$$

This has at most $q$ integers. Search it at literal words $w_{j_*}R^s$
using the same native procedure, then subtract the known $j_*q$.
No chosen-source fact was retained. The fixed anchor excludes nonzero
common translations of all ages, so Theorem 16.3's $q$-history
obstruction does not hold on this changed domain. If the anchor is
hidden, querying it requires the explicitly enlarged current permission;
its presence in a hidden partition alone does not provide its value.
Read at an absent suffix or at a previously queried address remains a
paid invocation under every one of these protocols. $\square$

**Mathematical citation 16.10 (suppliers, prior coverage and remaining gap).**
The native carriers and query interpretation are `Source` and
`substitution` in
[GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean),
and `Address`, `Reply`, `readout` in
[ActualTreeReadoutAcquisition](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean).
The acquired literal exterior and full hidden comparisons use
`literalRecord` and `canonicalRow_record_iff` in
[ActualCutPartitionDecoder](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean),
including its `eraseClasses` and `eraseClasses_literal` interpretation.
The right clock, physical `rights`, `right_clock_iterate` and exact
`right_clock_readout` in
[DelayedOriginalReadout](../../../D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout.lean)
are inspected at immutable
[1ca0bc3ada92f404ee3e9e1d5c236c73310013cf](https://github.com/the-omega-institute/trureturing/tree/1ca0bc3ada92f404ee3e9e1d5c236c73310013cf).
Its `clock_step` proof and the orbit recurrence in
[ActualFibonacciSupportChain](../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualFibonacciSupportChain.lean)
are supporting native suppliers. The support-chain result concerns
presence agreement; the all-branch argument in Theorem 16.6 supplies
the stronger full-reply statement needed here.

Sections 11, 13.3 and Reuse 14.2 supply the acquired factors and full
later-row collisions. Their zero-read graph bridge belongs to
[Transport--Memory Completion §8.2](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#82-标签恰须切开可能混淆的前缀).
The present unit does not require section 15. No age value or unknown
lag is supplied by the certified-epoch `original_decoder_service`:
that theorem has a given epoch, whereas the present output is the epoch
lag itself after discarding the original row.

At the same immutable pin,
[Native Birth Provenance §10](https://github.com/the-omega-institute/trureturing/blob/1ca0bc3ada92f404ee3e9e1d5c236c73310013cf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md#10-exact-class-root-experiments-on-every-full-actual-one-image-fiber)
uses bounded four-reply unrolling on a fixed complete current-row entry
after one authenticated update. A bounded tree at that fixed entry has
finitely many addresses. Here later acquired literal rows vary over
unbounded lags; a bound on each decision depth yields no common maximum
address across those entries, as Theorem 16.6 demonstrates.
[Acquired Relation History §31](https://github.com/the-omega-institute/trureturing/blob/1ca0bc3ada92f404ee3e9e1d5c236c73310013cf/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md#31-the-inherited-paid-consumer-and-the-retained-resource-boundary)
already separates epoch-uniform raw calls from epoch-dependent word
lengths under a certified-epoch original-row contract. That distinction
is reused; it supplies no forgotten-origin or unknown-lag decoder.

Charpenay--Le Treust--Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*, arXiv:2211.03649v2, Definition III.1 and Theorem III.4's
proof outline](https://arxiv.org/html/2211.03649v2), defines characteristic
edges by different target values at a common compatible side-information
value. This is the mature separation principle, not a new general
coloring theorem. Its probabilistic i.i.d. blocks, expected prefix-code
lengths and asymptotic rate objective do not establish the present
adversarial one-export alphabet price or native service costs.

Buhrman--de Wolf, [*Complexity Measures and Decision Tree Complexity*,
§3.1](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf), defines
adaptive query depth as the number of queried input variables on a
worst-case path. The native alphabet here has four replies and its tests
are finite words. This standard decision-tree viewpoint does not price
those words or grant hidden-subtree queries. Nowak,
[*The Geometry of Generalized Binary Search*, arXiv:0910.4397v5,
§V.A](https://arxiv.org/html/0910.4397v5), explicitly contrasts allowed
point tests with stronger dyadic-subinterval tests. Its binary-valued
hypothesis-space results are not transferred as a native halving oracle;
(NAR.16.12)--(NAR.16.14) establish the actual permitted partitions.

The coding and adaptive-query methods are literature-attested
ingredients. The full-current translation classification, attained
unknown-lag first-slot service, fixed-encoder feasibility construction
and uniform literal-address obstruction are repo-derived ordinary
mathematical deductions for Assumption 16.1. The compared owner, named
D5 suppliers and primary literature provide no directly matching
unknown-lag acquired-input service. This bounded comparison is not a
worldwide novelty assertion, exhaustive absence certificate or new
Lean/kernel verification.

The exact intermediate retained-memory versus call curve, minimum raw
calls for arbitrary encoders and menus, and joint address optimization
remain undetermined here. A faithful next mathematical gap is to
characterize which reply partitions of a finite compatible lag set are
realizable by one literal current-address Read, together with their
address lengths. Such a characterization would constrain joint encoder
and query choices; it is not needed for the endpoint and obstruction
proved above. Acquisition and authentication, all-native-source
extensions, total or peak memory, physical time and execution remain
outside these finite-family retained-reference results.

## 追加锚（本行以下为增补区）
