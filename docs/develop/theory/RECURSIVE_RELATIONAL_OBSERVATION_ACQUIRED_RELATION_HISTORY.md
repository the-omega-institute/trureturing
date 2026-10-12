# Actually acquired mixed-epoch relations and complete original recuts

## 1. Original sources, retained relations and the unchanged target

**Definition 1.1 (source and original row).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{ARH.1.1}
$$

These are nonempty finite free ordered trees; brackets, order and repeated
occurrences are part of the source. Addresses are finite words over
$\{L,R\}$, with root $\varepsilon$. The reply $r_t(p)$ lies in
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
A subtree $t|_p$ is defined only when $p\in\operatorname{Pos}(t)$.

For a finite prefix-free set $A$ of **original** addresses, use the complete
row $R_A(t)$ of [SLH, Definition 59.1][SLH]. Its reached holes are exactly
$A\cap\operatorname{Pos}(t)$, ordered lexicographically. Its concrete
outside context is obtained by replacing those whole subtrees by numbered
holes. Its partition equates two holes exactly when their complete ordered
subtrees are equal. An absent cut address supplies no hole. Empty cuts,
the root cut and cuts containing absent addresses are allowed.

Fix arbitrary such $P,Q$ and an actually acquired old row $R=(C,\pi)$ at
$P$. Let $\mathcal B$ be its set of classes. The old source correspondence from
[SLH, Theorem 59.4][SLH] is used without weakening:

$$
u=C[(z_{[i]})_i],\qquad z_b\in\mathcal T,
\qquad z_b\ne z_c\quad(b\ne c).
\tag{ARH.1.2}
$$

The occurrence list, every repeated class, every cross-class disequality,
the concrete outside and the old absent-address guards are retained.
Classes outside the new task still participate in (ARH.1.2).

**Definition 1.2 (signed, guarded relation history).** A literal record is
$(a,s,c)$ with certified epoch $a\ge0$, address $s$, and reply $c\in\mathcal A$.
A relation record is $e=(a,s,b,t,\bowtie)$, where $\bowtie$ is either
$=$ or $\ne$. Its predicate on an original source is

$$
\begin{aligned}
\operatorname{Rel}_e(u)\quad\Longleftrightarrow\quad&
 s\in\operatorname{Pos}(\rho^a u)\ \land\
 t\in\operatorname{Pos}(\rho^b u)\ \land\\
& (\rho^a u)|_s\ \bowtie\ (\rho^b u)|_t.
\end{aligned}
\tag{ARH.1.3}
$$

In particular, an absent endpoint makes either signed predicate false;
absence is not a disequality certificate. The compared objects are entire
trees, not their root replies. Endpoints can have different epochs and
can be absent originally but born before their recorded epochs.

For finite lists $H_0,H_{\rm rel}$, retaining repetitions, set

$$
\begin{aligned}
U=\mathcal U_R(H_0,H_{\rm rel})
 :=\{u\in\mathcal T:;&R_P(u)=R,\\
&r_{\rho^a u}(s)=c\quad((a,s,c)\in H_0),\\
&\operatorname{Rel}_e(u)\quad(e\in H_{\rm rel})\}.
\end{aligned}
\tag{ARH.1.4}
$$

All constraints refer to this same $u$. Throughout the service statements,
$U\ne\varnothing$ and the task is the **entire** $R_Q(u)$: its concrete
outside, reached original holes and complete equality partition. No past
raw event is requested.

**Assumption 1.3 (paid acquisition, complete cut and service).** The retained
records were acquired by legal finite paid raw acquisition and comparison
before a complete access cut. The same physical register, with the same
original root and source, has actually reached a certified
$N\ge\max(\{0\}\cup\operatorname{epochs}(H_0,H_{\rm rel}))$.
The entire accessible initial state is a fixed function of the stated
records and common parameters, and recovers them. Its original-source
fiber is exactly (ARH.1.4). A source-dependent choice of records or of
control state must satisfy this correspondence too.

Every still accessible source-bearing cache, address, count, length,
program position, timing field, output, archive, permission or handle is
included in the complete retained input. No forgotten traversal or acquired
tree description is available. This is an access assumption, not a claim
of physical erasure. Source continuity and epoch certification do not
supply a source identity label. If these conditions fail, the appropriate
fiber must include the extra state; it is not (ARH.1.4).

A service is deterministic, effective and terminates correctly for every
$u\in U$. The allowed operations are paid $\mathsf{Read}(p)$ at any finite
physical address, including absent addresses, and real serial
$\mathsf{ApplyRho}$ on that register. A static service makes no further
updates. There is no reset, reroot, clone, unknown whole-tree, unknown
subtree equality, source-membership or identity port. Local computation
uses common input and acquired replies only. Updates reveal no additional
source-dependent timing or implementation information.

A uniform finite new-read budget means a single $K\in\mathbb N$, depending
on common retained input and task, bounds new raw calls on **all** $u\in U$.
Physical address generation and length, local work, installation, memory,
retention, entry, version evidence, updates, archives and output are charged
separately. A finite per-source pre-cut cost is not required to have a
uniform bound. A new entry after an absorbing halt must be supplied and
paid separately. These are the same operation and access conditions as
[SLH, §§1, 59, 62 and 74][SLH], with the additional acquired predicates
(ARH.1.3).

## 2. Acquisition correspondence and the inherited existence bridge

**Proposition 2.1 (an actual producer for the full signed input).** Fix a
finite public list of literal coordinates, a finite public list of endpoint
pairs, $P$, and a final epoch $N$ at least their epochs. There is a
deterministic source-total pre-cut acquisition procedure whose successful
retained outputs have exactly the fibers (ARH.1.4), conditional on the
complete cut in Assumption 1.3. An unreachable endpoint produces a distinct
invalid-record outcome, not a successful signed record.

Proof. Use the paid full traversal of [SLH, §§53 and 59][SLH] at epoch zero
to compute $R_P(u)$, including all old comparisons. Process the public
epochs in increasing order, executing each intervening update on the same
register. Perform every requested literal read. For each endpoint $(a,s)$,
read $s$ at epoch $a$. If reached, acquire its complete finite subtree by
the same traversal, prefixing every relative request by $s$ and requesting
children only after their parent reports branch. Keep these paid finite
descriptions until both endpoints of each comparison have been obtained.
Finite syntactic tree comparison then determines its sign. A comparison
can be computed after the earlier endpoint's epoch without accessing that
old physical version: its paid description was still available before
the cut. These descriptions are not physical register clones.

Continue to $N$ and retain the canonical old row, stipulated literal
replies, endpoint coordinates and signs, $N$, and common code, permissions
and ready control. Apply the stipulated complete cut to the descriptions
and all other source-dependent acquisition fields. On any source the
successful retained output reports exactly the predicates in Definition
1.2. Conversely, any finite source satisfying a fixed successful output
executes the same public coordinate schedule, gives its stated replies and
signs, and reaches that same retained state. Its forgotten traversal length
can differ. These two directions prove the fiber equality, not merely
soundness of each record separately.

For a non-sharing traversal, successful pre-cut raw cost is

$$
|\operatorname{Pos}(u)|+|H_0|
 +\sum_{(a,s)\in E}|\operatorname{Pos}((\rho^a u)|_s)|,
\tag{ARH.2.1}
$$

where $E$ lists endpoint occurrences with repetitions; their root reads
are already counted in their traversals. Every physical request includes
its actual prefix. Comparisons, descriptions, updates, certification and
the access cut have their separate costs. All are finite on each source;
none is refunded by the short retained sign. The procedure computes both
sign outcomes, so fixing either actual outcome is legitimate. An adaptive
producer requires its own full control/state correspondence; legality
alone does not make its selection rule disappear. $\square$

**Definition 2.2 (finite original-prefix determination).** For the entire
fiber (ARH.1.4), write $\operatorname{PrefDet}(U,Q,h)$ for

$$
\forall u,v\in U,\quad
\bigl[\forall s, |s|\le h\Longrightarrow r_u(s)=r_v(s)\bigr]
\Longrightarrow R_Q(u)=R_Q(v).
\tag{ARH.2.2}
$$

The following correspondence is an application of the operational part
of [SLH, Theorem 74.4, proof (iii), and (SLH.74.7)][SLH], not a new
literal-history algorithm:

$$
\begin{aligned}
&\text{uniform-finite-read serial service on }U\\
\Longleftrightarrow\;&\text{uniform-finite-read static service on }U\\
\Longleftrightarrow\;&\exists h\ge0\ \operatorname{PrefDet}(U,Q,h).
\end{aligned}
\tag{ARH.2.3}
$$

Here is the precise change of domain needed to use that supplier. Its
serial-to-prefix direction uses a common complete initial state,
source-totality, four-valued replies and physical-address locality. Those
hypotheses hold in Assumption 1.3 independently of the form of $U$.
The supplier compresses each deterministic computation/update segment
between replies and obtains a finite reply tree under a uniform $K$.
Its finitely many submitted addresses have a finite maximum length.
(SLH.74.7) turns that length into an $h$ satisfying (ARH.2.2), including
all born and absent-address cases. It also gives at most $4^K$ terminal
outputs. No prior uniform bound on local work or update count is added.

For the converse the old literal-only feasibility routine is replaced
as follows. Membership of a *given concrete finite candidate* in (ARH.1.4)
is decidable by computing its old row, finite iterates, literal replies,
endpoint guards and complete signed comparisons. Given a valid $h$, use
[SLH, Theorem 2.2][SLH] at the actual static epoch $N$ to recover all original
replies of length at most $h$. This costs at most
$2(2^{h+1}-1)$ new reads, with address length at most $h+\lceil N/2\rceil$.
Enumerate all finite original trees by size and encoding until one belongs
to $U$ and agrees with the recovered prefix. The actual source is an
enumerated witness, so this local search terminates on every actual run.
Output its complete $R_Q$. Equation (ARH.2.2) proves that output is common
to the actual conditioned fiber. No claim that the witness is the real
source is needed. The newly acquired evidence is the actual $N$-epoch
reply tuple, not fictitious epoch-zero events. Static inclusion gives
the remaining direction of (ARH.2.3).

This constructs a service **given** a suitable $h$. It does not decide
whether an $h$ exists for arbitrary $H_{\rm rel}$, extract it from arbitrary
source-total code, or decide emptiness of arbitrary coupled morphic
constraints. It proves equality of the two existence predicates, not
equality of their minimum budgets. These distinctions remain part of the
full question in §9.

## 3. Guarded morphic cells and exact paid reuse

**Definition 3.1 (residual terms).** Use [SLH, Definition 74.2][SLH] with

$$
d=1+\max\bigl(\{0\}\cup\{|q|:q\in Q\}
 \cup\{|s|:(a,s,c)\in H_0\}
 \cup\{|s|,|t|:(a,s,b,t,\bowtie)\in H_{\rm rel}\}\bigr).
\tag{ARH.3.1}
$$

For each old class choose its original depth-$d$ prefix pattern $t_b$,
using one variable at each reached depth-$d$ frontier position, different
variables for different classes and positions, and the same pattern at
every occurrence of a repeated class. Put

$$
W_\eta=C[(t_{[i]})_i],\qquad
\Delta_\eta=\{t_b\ne t_c:b<c\}.
\tag{ARH.3.2}
$$

The finite pattern list and the literal checks are exactly the existing
construction, including all old disequalities. A residual term is a finite
ordinary term over $\alpha,\beta,\langle\ ,\ \rangle$ and these variables.
A morphic expression $\rho^a(A)$ means the actual iterate applied **after**
a finite-tree valuation of $A$; $\rho$ is not a free new constructor.

**Proposition 3.2 (full-domain guarded representation).** There is an
effective finite list of disjoint original prefix cells such that the
entire $U$ is their union under $v\mapsto W_\eta[v]$. Each cell retains
$\Delta_\eta$, its literal conditions, and a finite conjunction of signed
relations between morphic residual terms or concrete trees. Empty cells
may remain in the list. The construction does not require a general
emptiness algorithm. It also computes the full target maps on each cell.

Proof. A residual occurrence has depth $|p_i|+d$, strictly beyond every
named endpoint, literal and new cut address. Thus navigation to an endpoint
$s$ either reaches an original subterm $A$ of $W_\eta$, in which case the
whole endpoint at epoch $a$ is $\rho^a(A[v])$, or meets a known original
leaf $\lambda_b$ at a strict prefix $c$ of $s$. Here
$\lambda_0=\alpha$, $\lambda_1=\beta$. In the latter case write $s=cz$.
The supplied leaf-sector formula [SLH, Definition 29.1][SLH] gives the guard

$$
a+b\ge w(z^-)+2,
\qquad w(z)=\#_L(z)+2\#_R(z),
\tag{ARH.3.3}
$$

and, when it holds, the complete endpoint is
$T_{a+b-w(z)}$, where $T_j=\rho^j\alpha$. If the guard fails, reject the cell
for this relation record, for either sign. In the original-node case the
endpoint is always reached. Concrete computations cover ground $A$ too.
Apply this to both endpoints of every relation and retain the stated sign
between the resulting **whole** expressions. Literal checks use the
already supplied guarded reply formula, including repetitions and absent
replies.

Each concrete old class value has a unique pattern and a unique valuation
by its original frontier subtrees. The inverse to filling is recovered at
old representative holes and then at their pattern frontiers. [SLH,
Theorems 59.4 and 60.2][SLH] supply exactly the old-row correspondence.
The endpoint analysis proves each newly attached predicate equivalent to
(ARH.1.3) under that same valuation. Therefore the disjoint union of all
satisfying valuations is bijective with (ARH.1.4). No product relaxation,
separate marginal feasibility or chosen representative is involved.

The target construction of [SLH, (SLH.74.9)][SLH] still applies: navigation
to $Q$ gives a fixed reached set $J_\eta$, a symbolic outside context
$E_\eta$ and subterms $A_{\eta,q}$, satisfying

$$
\begin{aligned}
I_Q(W_\eta[v])&=J_\eta,\qquad C_Q(W_\eta[v])=E_\eta[v],\\
q\sim r&\Longleftrightarrow
 A_{\eta,q}[v]=A_{\eta,r}[v]\quad(q,r\in J_\eta).
\end{aligned}
\tag{ARH.3.4}
$$

The outside can contain residual variables which must be output as complete
concrete trees. Equation (ARH.3.4) keeps that obligation.

For clarity about the algebraic boundary, when $a\le b$, injectivity from
[TRANSPORT, (RA.2207)][TRANSPORT] gives

$$
\rho^a(A[v])=\rho^b(B[v])
\Longleftrightarrow A[v]=\rho^{b-a}(B[v]),
\tag{ARH.3.5}
$$

and the same equivalence for disequality. Only the common iterate cancels.
If one endpoint is a known concrete $g$, its finite partial image inverse
$\delta$ from the same supplier tests whether $g\in\rho^a[\mathcal T]$.
When so, $\rho^a(A[v])=g$ is exactly $A[v]=\delta^a(g)$; otherwise it is
always false. The corresponding reached disequality is its complement.
Equal epochs therefore give ordinary signed term constraints; a known
endpoint does too. Unequal live epochs generally leave a morphic relation.
For instance $\rho(x)=\langle y,z\rangle$ has
$(x,y,z)=(\beta,\beta,\alpha)$ as a solution. Treating $\rho$ as a free
constructor would reject it. The original source
$u=\langle\beta,\alpha\rangle$ satisfies $(0,L,1,R,=)$ although its
original children differ. $\square$

The following paid reductions identify existing supply used by this
representation and by later consumers; they are not new solvers.

If a record compares two reached old holes at the **same** epoch, [SLH,
Theorem 60.2][SLH] determines its sign from the complete old partition.
A consistent record is redundant; an inconsistent one violates the
nonempty-input promise. All other old classes and their disequalities stay.
Here [SLH, Theorem 74.4][SLH] applies directly when no other nonredundant
relation remains. [SLH, Theorem 69.4][SLH] applies to its own finite VALUE
tasks, with its static contract and exact minimax conclusion unchanged.

For records whose cell expressions have a concrete endpoint, acquire the
finite original prefix needed to select a cell using [SLH, Theorem 2.2][SLH].
The actual current reply tuple entails that prefix on all old-row/literal
sources. For each remaining nonconstant predicate $u|_a=g$, the selected
cell guarantees that $a$ is originally reached; use the paid delayed
whole-template certificate [SLH, Theorem 55.3][SLH] under the physical prefix
$a$. Its complete actual reply tuple decides both equality and disequality
against $g$, on every originally reached finite subtree, without a shape
promise. Templates are computed from common data and the selected cell.
They are not unknown-source descriptions.

To verify the exact interface, let $H'$ contain $H_0$ and all those actual
current replies. On a reached branch of this converter, every source in
$\mathcal U_R(H')$ has the selected original prefix and the same template
test outcomes, hence satisfies every incoming relation. Conversely any
incoming source giving the tuple belongs to $\mathcal U_R(H')$. The new
full branch fiber is therefore exactly that basic old-row/literal fiber.
A rejected template is represented by its actual mismatching tuple, not
an invented historical event. There are finitely many cells and finite
template supports. Their union provides a uniform finite read bound;
all branch feasibility and subsequent full-row decisions can now use
[SLH, §§61 and 74][SLH]. Incoming bounded solvability restricts to every
branch, and bounded branch services combine with the paid converter using
a finite maximum. Thus this is also an exact existence reduction for this
case. It adds no new mathematical criterion to the predecessor.

A second direct interface is a fully acquired row at another known original
frontier $A$: retained literals determine its entire outside context and
reach guards, and same-epoch records determine its complete partition.
It can be computed from already paid data. To replace the old input by
this row and literal history, **both** full source-fiber inclusions must
hold; the old row and every remaining record must be consequences of the
new input, and conversely. Under that condition only a paid local encoding
change is needed. Dropping old off-task disequalities would violate it.
An ordinary same-epoch equation without such a correspondence does not
by itself constitute an acquired row input.

An unselected finite union of basic fibers is not this paid interface.
For example, the union of the equal-child and unequal-child two-hole
rows is the whole set of original pairs; knowing the separate row on
each part would already decide the unbounded child-equality task. On the
union, pairs $\langle z,z\rangle$ and $\langle z,z'\rangle$, with $z,z'$
agreeing arbitrarily deeply but unequal, obstruct finite-prefix determination
of the two-hole row. The caller has no free branch selector. The stronger
nonreduction statements in §8 concern exact entire fibers.

## 4. Root-to-descendant certificates and the supplied atomic orbit

**Definition 4.1 (root-certificate fragment and orbit suppliers).** A retained
input is in the fragment when it contains a positive record

$$
e=(n,\varepsilon,m,p,=),\qquad p\ne\varepsilon,
\tag{ARH.4.1}
$$

possibly written with its endpoints exchanged. All other old data and
finite signed mixed histories remain arbitrary. Recognition means finding
such a record; it does not require proving that every equivalent presentation
has one.

Use the existing atomic recurrence and transport clock:

$$
\begin{gathered}
T_0=\alpha,\quad T_1=\beta,\quad
T_{j+2}=\langle T_{j+1},T_j\rangle,\qquad \rho^aT_j=T_{j+a},\\
\kappa(\alpha)=0,\quad\kappa(\beta)=1,\quad
\kappa(\langle x,y\rangle)=2+\kappa(y),\quad
\kappa(\rho^a u)=\kappa(u)+a.
\end{gathered}
\tag{ARH.4.2}
$$

These are [TRANSPORT, §§23–24][TRANSPORT] and the atomic supply used by
[SLH, §§2 and 29][SLH]. In particular $\kappa(T_j)=j$, so the $T_j$ are
pairwise distinct. Their reached-subtree formula is

$$
\begin{aligned}
s\ne\varepsilon:\quad
s\in\operatorname{Pos}(T_j)&\Longleftrightarrow j\ge w(s^-)+2,\\
T_j|_s&=T_{j-w(s)}\quad\text{when reached};
\end{aligned}
\tag{ARH.4.3}
$$

at the root the guard is automatic. Nonnegative $j-w(s)$ alone is not
a reach test, as $s=LL,j=2$ shows.

The exact previously established orbit classification used here is the
first conjunct of [SourceTransportCentralizer,
`source_transport_centralizer`][CENTRALIZER]:

$$
\operatorname{Stab}(v):=
[\rho^2v=\langle\rho v,v\rangle]
\quad\Longleftrightarrow\quad
\exists j\ge0, v=T_j.
\tag{ARH.4.4}
$$

Its `Source = FreeMagma Bool` identifies `.of true` with $\alpha$,
`.of false` with $\beta$, and `FreeMagma.mul` with ordered pairing;
`GenealogicalFiberTransport.substitution` is exactly (ARH.1.1).
The classification itself is supply, not a new theorem of this volume.

**Theorem 4.2 (exact acquired root-certificate fiber).** For arbitrary
$n,m\ge0$ and nonempty $p$, the guarded record (ARH.4.1) has a source if
and only if $m=n+w(p)$. More precisely, its entire fiber before intersection
with other retained conditions is empty unless this equality holds, and
otherwise is

$$
\{T_k:k\ge e\},\qquad
 e=\begin{cases}1,&n=0\text{ and the last letter of }p\text{ is }L,\\
                 0,&\text{otherwise}.
   \end{cases}
\tag{ARH.4.5}
$$

This is a consequence of an acquired predicate on all finite original
trees; membership in an orbit is not an additional source promise.

Proof. If $m\le n$, each application of $\rho$ weakly increases node count,
as follows immediately from its two leaf images and distribution over a
pair. But the reached nonroot subtree of $\rho^m u$ has strictly fewer
nodes than $\rho^m u$. It cannot equal $\rho^n u$. This rules out these
epoch orders and agrees with $w(p)>0$.

Suppose $m>n$ and put $d=m-n$. We first establish the interface to
(ARH.4.4). For any finite $v$, if $p$ is reached in $\rho^d v$ and
$v=(\rho^d v)|_p$, then $\operatorname{Stab}(v)$. Use strong induction on
the node count of $v$, keeping $d,p$ fixed. If $p$ is an original reached
address of $v$, let $z=v|_p$, a strict subtree. Original-address transport
[TRANSPORT, (RA.2205)–(RA.2206)][TRANSPORT] gives $v=\rho^d z$.
Consequently $z=(\rho^d z)|_p$: indeed $\rho^d z=v$ and $v|_p=z$.
The induction hypothesis yields $\operatorname{Stab}(z)$. Apply $\rho^d$
to its equation and distribute over pairing to obtain
$\operatorname{Stab}(\rho^d z)=\operatorname{Stab}(v)$.

If $p$ is not an original address of $v$, a known original leaf
$\lambda_b$ blocks it at a strict prefix $a$, so $p=as$ with $s\ne\varepsilon$.
Its reached later endpoint belongs to that leaf sector. By (ARH.4.3) and
the reach guard it is $T_{d+b-w(s)}$ with a nonnegative index. It equals
$v$ by hypothesis. The reverse implication of the supplied (ARH.4.4)
gives $\operatorname{Stab}(v)$. This includes the case that $v$ is a leaf.
The only recursive call was on the strictly smaller $z$, completing the
induction. We have proved a certificate-to-stability bridge, without
reproving the supplied stability classification.

Apply the bridge and (ARH.4.4) to the mathematical tree $v=\rho^n u$.
This changes no physical register. Thus $v=T_j$ for some $j$. By (ARH.4.3),
its record is now exactly

$$
T_j=T_{j+d-w(p)},\qquad j+d\ge w(p^-)+2.
\tag{ARH.4.6}
$$

Index injectivity gives $d=w(p)$. Under this equality the reach condition
is $j\ge2-w(a)$, where $a$ is the last letter of $p$.
The clock gives $j=\kappa(u)+n\ge n$. Injectivity of $\rho^n$ and
$T_j=\rho^nT_{j-n}$ imply $u=T_{j-n}$. Writing $k=j-n$, the two lower
bounds are exactly $k\ge e$ in (ARH.4.5): the last-letter requirement is
one for $L$ and zero for $R$, and a positive $n$ already supplies the one.
Conversely every listed $T_k$ satisfies both the reach guard and equality
in (ARH.4.6). Proposition 2.1 acquires that record by paid traversal at its
two epochs. Every and only these sources produce its positive outcome;
no retained index, size or traversal count is needed. $\square$

The instance $(a,\varepsilon,a+2,R,=)$ selects the entire orbit for every
$a\ge0$. The instance $(0,\varepsilon,1,L,=)$ selects $k\ge1$.
In the first instance the descendant can be born after epoch zero even
when $u$ is a leaf. These are uses of the same guarded statement.

## 5. Effective finite/cofinite indices for the entire retained input

**Definition 5.1 (complete cut and row height).** A finite prefix-free
address set $A$ is complete when every infinite $L/R$ path has a prefix
in $A$. This is decidable from its finite trie: every node before a cut
leaf must have both children in the trie. The empty cut is incomplete;
$\{\varepsilon\}$ is complete. Let $\operatorname{ht}(C)$ be the ordinary
finite height of a context with holes treated as leaves.

For an incomplete $A$ one can compute an address $r$ incomparable with
every member of $A$. For $A=\varnothing$ take $r=\varepsilon$; otherwise
follow a missing branch of its finite trie and extend past the maximum
cut depth. Thus no cut removes or enters any part of the cone at $r$.

**Theorem 5.2 (exact index compiler with all old constraints).** Suppose the
input contains a record from Definition 4.1. There is an effective procedure
which either detects its incompatible epoch/weight condition, or computes
an integer $B\ge e$, a finite $S_0\subseteq\{e,\ldots,B-1\}$ and
$\tau\in\{0,1\}$ such that

$$
U=\{T_k:k\in S\},\qquad
S=S_0\ \cup\ \begin{cases}\{k:k\ge B\},&\tau=1,\\
                              \varnothing,&\tau=0.
             \end{cases}
\tag{ARH.5.1}
$$

Here $P,R,H_0$ and **every** additional finite signed mixed-epoch relation
are arbitrary. All predicates are checked jointly on the same $T_k$.
The procedure detects emptiness too; under the nonempty promise it is
excluded. An infinite tail in (ARH.5.1) denotes all its indices.

Proof. An incompatible designated record gives emptiness by Theorem 4.2.
Otherwise that theorem first restricts all and only possible sources to
$T_k$, $k\ge e$. We give explicit eventual thresholds for every remaining
condition and evaluate the finite part exactly.

For a literal $(a,s,c)$, at

$$
k\ge B_{a,s}:=\max(0,w(s)+2-a)
\tag{ARH.5.2}
$$

its reply on $T_k$ is branch. This inequality guarantees the reach guard
as well as index at least two; for the root it still suffices.
Consequently the eventual truth of that literal is exactly
$c=\mathsf{branch}$. Small indices use the guarded formula of [SLH,
Definition 29.1][SLH]. In particular, absent and repeated replies are
not discarded.

For an endpoint $(a,s)$ define

$$
G_{a,s}=\begin{cases}
0,&s=\varepsilon,\\
\max(0,w(s^-)+2-a),&s\ne\varepsilon.
\end{cases}
\tag{ARH.5.3}
$$

Above $\max(G_{a,s},G_{b,t})$ both endpoints of a relation are reached.
Their whole values are $T_{k+a-w(s)}$ and $T_{k+b-w(t)}$. They are equal
if and only if

$$
a-w(s)=b-w(t).
\tag{ARH.5.4}
$$

For a disequality use the opposite comparison of these integers.
This computes its eventual truth for arbitrary epochs and original or
born endpoints. Below the threshold test both reach guards before either
sign. A negative index is never substituted into $T$.

The old row needs a whole-context check. If $P$ is complete, put

$$
B_P=\max\bigl(\{0\}\cup
        \{w(p^-)+2:p\in P,\ p\ne\varepsilon\}\bigr).
\tag{ARH.5.5}
$$

For every $k\ge B_P$ all cuts are reached. Completeness says their trie
is the entire outside context, with branch nodes at proper prefixes and
holes at $P$. The old hole values are $T_{k-w(p)}$; their complete
partition identifies precisely equal weights $w(p)$. Thus the entire
old row is one effectively constructed constant row on this tail.
Compare it with all of $R$, including its context and complete partition,
to decide the old row's eventual truth. This also covers the root cut.

If $P$ is incomplete, compute an incomparable $r$ as in Definition 5.1.
For

$$
k\ge B_P:=w(r)+\operatorname{ht}(C)+2,
\tag{ARH.5.6}
$$

$r$ is reached in $T_k$ and its entire subtree $T_{k-w(r)}$ survives in
the old outside. The recurrence (ARH.4.2) gives
$\operatorname{ht}(T_j)=j-1$ for $j\ge1$ by induction, with
$\operatorname{ht}(T_0)=0$. This surviving subtree has height greater
than $\operatorname{ht}(C)$, so the old context cannot equal $C$.
The eventual old-row truth is therefore false. For empty $P$, $r$ is
root and this is simply the finite height obstruction for a fully
concrete old row.

Take $B$ at least $e$, $B_P$, all thresholds (ARH.5.2), and all endpoint
thresholds (ARH.5.3). Let $\tau$ be the conjunction of the eventual old-row,
literal and signed relation truth values. For each $e\le k<B$, directly
compute the finite row $R_P(T_k)$ and all literal and guarded signed
predicates; include $k$ in $S_0$ exactly when the entire conjunction holds.
These are finite computations on known candidate trees, not source queries.

Theorem 4.2 excludes every non-orbit source. The finite checks are exact
below $B$, and the displayed thresholds prove constant truth at **every**
$k\ge B$. This proves both inclusions in (ARH.5.1), including all old
repetitions and off-task inequalities. It also proves emptiness exactly
when $S_0=\varnothing$ and $\tau=0$. The finite initial list is not a
finite proxy for the infinite tail. $\square$

## 6. An effective complete-row decision and paid consumer on this fragment

**Theorem 6.1 (full original recut criterion).** Under Assumption 1.3 and
Definition 4.1, let $(S_0,B,\tau)$ be the exact nonempty description from
Theorem 5.2. For every allowed $N$, the following are equivalent:

1. A deterministic effective source-total serial service recovers the
   entire original $R_Q$ with a uniform finite new-read budget.
2. Such a static service exists at $N$.
3. $\tau=0$ or $Q$ is complete.

The third condition is effectively decidable from the common input and
$Q$. In the positive cases one can construct a static consumer and a
finite read bound independent of $N$, with addresses depending on $N$.
In the negative case the obstruction holds on the entire given fiber,
including all additional retained constraints.

Proof. On the whole orbit $\kappa(T_k)=k$. The supplied right-spine reply
formula in [SLH, §2][SLH] gives, at physical epoch $N$,

$$
\begin{array}{c|cccc}
r_{T_{N+k}}(R^a)&\mathsf{absent}&\alpha&\beta&\mathsf{branch}\\
\hline
N+k&<2a&2a&2a+1&\ge2a+2.
\end{array}
\tag{ARH.6.1}
$$

For a known candidate $j$, one paid read at
$R^{\lfloor(N+j)/2\rfloor}$ tests $k=j$: accept just the leaf reply
$\alpha$ if $N+j$ is even, or $\beta$ if it is odd. Equation (ARH.6.1)
proves both directions **on the entire orbit fiber**. This is a use of
the supplied clock, not a new unknown-tree equality port; outside the
orbit, a clock match would not identify a tree.

If $\tau=0$, $S=S_0$ is finite and nonempty. Test candidates in a fixed
order except the last. On a match compute and output the complete
$R_Q(T_j)$; on no match use the last candidate. The exact fiber formula
proves source-total correctness. A sufficient budget is
$|S_0|-1$, including zero for a singleton. All missing original $Q$
addresses and their concrete outside portions are computed from the
identified original tree. No current recut is substituted for it.

Suppose $\tau=1$ and $Q$ is complete. Define

$$
B_Q=\max\bigl(\{0\}\cup\{w(q^-)+2:q\in Q,\ q\ne\varepsilon\}\bigr),
\quad D=\max(B,B_Q),\quad A=S\cap\{0,\ldots,D-1\}.
\tag{ARH.6.2}
$$

The finite $A$ is effectively obtained from (ARH.5.1). For every $k\ge D$
all $Q$ addresses are originally reached. The entire outside is the
complete finite trie of $Q$, with its leaves replaced by the numbered
holes. Its complete partition is

$$
q\sim r\quad\Longleftrightarrow\quad w(q)=w(r).
\tag{ARH.6.3}
$$

Indeed the full hole values are $T_{k-w(q)}$ and $T_{k-w(r)}$ and their
indices are injective. Thus (ARH.6.3) and the trie give one **complete row**
for every source in the allowed tail, even though their unknown hole values
are unbounded.

Test every $j\in A$ by (ARH.6.1). A match selects its exact finite-tree
row; if all reject, the exact source characterization implies $k\ge D$,
so output the complete tail row. The read budget is at most $|A|$.
There is no read in the tail branch beyond those finitely many tests and
no new update. If $Q=\{\varepsilon\}$, its single-hole row is constant
on all sources and can instead be returned with zero reads. Either
consumer handles the boundary, without a minimum-budget claim.

For comparison with the existing template interface, the same positive
construction may test each finite candidate by the delayed whole-tree
certificate of [SLH, Theorem 55.3][SLH]. Summing its $\ell(T_j)$ costs
gives another sufficient bound valid even against arbitrary finite
non-orbit competitors. The smaller displayed bounds here use the actually
retained orbit consequence. Both methods pay their real raw requests.
They are consumers of Theorem 5.2, not replacements for its entire-fiber
proof.

For necessity suppose $\tau=1$ and $Q$ is incomplete. Choose $r$
incomparable with every $q\in Q$. For all sufficiently large allowed
$k\ge B$, $r$ is reached, and the whole subtree $T_{k-w(r)}$ is part of
the **concrete outside** of $R_Q(T_k)$. No $Q$ hole meets that cone. As
$k$ varies through this tail those subtrees are pairwise distinct, giving
infinitely many complete target rows on this very $U$. The inherited
finite-transcript argument in §2 permits at most $4^K$ terminal outputs
for any uniform $K$-read serial service. Such a service cannot output
this infinite image.

There is also a direct full-fiber witness to failure of (ARH.2.2).
For any proposed $h$, choose distinct allowed $k,l$ sufficiently large
that $k,l\ge2h+2$ and the preceding $r$ is reached. At every original
address of length at most $h$, both sources reply branch by (ARH.4.3).
Their full outside subtrees at $r$ differ. They satisfy all retained
conditions because both belong to the exact tail of (ARH.5.1), yet their
complete $Q$ rows differ. This witness excludes static and real serial
services by (ARH.2.3). It does not discard any old disequality.

We have proved $3\Rightarrow2\Rightarrow1\Rightarrow3$. All finite
candidate construction, row computation and integer/trie work terminate.
The tests use the same register at $N$. A test for $j$ has physical address
length $\lfloor(N+j)/2\rfloor$; the length sum is the sum over actual
tests. Template alternatives have exactly the separately stated address
costs in [SLH, §55][SLH]. Computation, stored descriptions, installation,
entry, certification, archives and complete output are additional costs.
These statements bound new raw calls only, and make no general minimax
or joint-resource optimality assertion. $\square$

Outputting the row does not create a new access cut that forgets
$R,H_0,H_{\rm rel}$ or the new actual replies. Subsequent source fibers
still include every accessible field, as in [SLH, Proposition 68.3 and
(SLH.72.5)][SLH]. In particular, the positive tail branch is justified by
the retained relation, not by a fabricated acquisition of its unknown
whole trees.

## 7. A native four-hole complete-row consumer

**Proposition 7.1 (one read on an entire acquired relation fiber).** Take

$$
\begin{gathered}
P=\{L,R\},\quad C=\langle\square_1,\square_2\rangle,
\quad \pi=\{\{1\},\{2\}\},\quad H_0=\varnothing,\\
H_{\rm rel}=\{(0,\varepsilon,1,L,=)\},\quad
Q=\{LL,LR,RL,RR\},\qquad N\ge1.
\end{gathered}
\tag{ARH.7.1}
$$

The entire input fiber is $U_\star=\{T_j:j\ge2\}$. Its complete original
$Q$ row is one of the following three rows:

$$
\begin{array}{c|c|c|c}
j&\text{reached original cuts}&\text{outside context}&\text{partition}\\
\hline
2&\varnothing&\langle\beta,\alpha\rangle&\varnothing\\
3&LL,LR&\langle\langle\square_1,\square_2\rangle,\beta\rangle
 &\{\{1\},\{2\}\}\\
\ge4&LL,LR,RL,RR
 &\langle\langle\square_1,\square_2\rangle,
                 \langle\square_3,\square_4\rangle\rangle
 &\{\{1\},\{2,3\},\{4\}\}.
\end{array}
\tag{ARH.7.2}
$$

For each allowed $N$, both static and serial minimum new-read budgets
for this particular complete-row task are exactly one. Removing the
relation record, while keeping the same old row and same $Q$, leaves
no uniform finite-read service.

Proof. Theorem 4.2 gives $j\ge1$ before the old-row intersection.
$T_1$ is a leaf and fails that old row; for every $j\ge2$, the root
children are $T_{j-1},T_{j-2}$, which are distinct. Thus exactly
$j\ge2$ remain. In particular the old disequality has been enforced,
not dropped. Proposition 2.1 gives a legal paid acquisition: retain the
acquired epoch-zero root description until after one real update, acquire
the whole current subtree at $L$, compare the two descriptions, and
then perform the stipulated full cut. Continuing to $N$ adds actual paid
updates. Neither $j$ nor either tree description is retained.

For $j=2$, both original children are leaves, so every $Q$ address is
absent. For $j=3$, only the original left child is a pair and the right
child is $T_1=\beta$. For $j\ge4$ all four cuts are reached, and their
whole values in the displayed order are

$$
T_{j-2},\quad T_{j-3},\quad T_{j-3},\quad T_{j-4}.
\tag{ARH.7.3}
$$

Index injectivity gives the full partition in (ARH.7.2), including the
cross-parent repeated class. This proves the three complete rows.

At the actual current tree $T_{N+j}$, read just

$$
R^{\lceil(N+2)/2\rceil}.
\tag{ARH.7.4}
$$

If $N$ is even, replies $\alpha,\beta,\mathsf{branch}$ select,
respectively, the first, second and third rows of (ARH.7.2); absent is
unreachable. If $N$ is odd, absent selects the first, $\alpha$ the
second, and $\beta$ or branch the third. This table is the direct
substitution of the address exponent into (ARH.6.1), so it is valid for
all $j\ge2$, not just the first few sources. The actual read selects a
whole row, not merely an equality bit. Its address length and all local
row construction/output work remain paid.

Zero new reads leave the same deterministic control on $T_2$ and $T_3$,
even if real updates are executed without observations. Their required
complete rows differ, excluding zero reads in both service classes.
Together with (ARH.7.4) this proves the asserted example-specific minimum.

Finally remove the relation. For any $h$, choose distinct finite trees
$z,z'$ with the same original replies through depth $h$. Such a pair is
obtained by a full binary tree with leaves deeper than $h$ and a change
of one deepest label. The two original sources

$$
u=\langle\langle z,z\rangle,\alpha\rangle,
\qquad v=\langle\langle z,z'\rangle,\alpha\rangle
\tag{ARH.7.5}
$$

have that same two-hole old row: the original left child is a pair and
therefore differs from the right leaf. They agree through original depth
$h$. Their only reached $Q$ cuts are $LL,LR$; these are equal in $u$
and unequal in $v$, with the same concrete right outside $\alpha$.
Thus their complete rows differ. [SLH, Theorem 74.4][SLH], or its inherited
prefix obstruction in §2, excludes a uniform finite serial budget on
this whole basic fiber. Its full target image is nevertheless finite: each
original root child is either one of two concrete leaves or a pair whose
two children are holes; there are finitely many such contexts and
partitions of at most four holes. Thus finite target image alone does not
suffice. The change in solvability comes from the actually retained
relation while the full-row task is unchanged. $\square$

## 8. Limits of exact compilation to ordinary old inputs

**Definition 8.1 (ordinary coordinate-preserving cell).** An ordinary cell
in tree coordinates $(x,y)$ is a relation defined by

$$
\exists z_1,\ldots,z_s\in\mathcal T\quad
 \bigwedge_i A_i(x,y,\mathbf z)=B_i(x,y,\mathbf z)
 \ \land\ \bigwedge_j C_j(x,y,\mathbf z)\ne D_j(x,y,\mathbf z),
\tag{ARH.8.1}
$$

where every expression is a finite free term over the original two
leaves and ordered pair. Finite ground tree parameters are allowed.
There is no interpreted $\rho$ or encoded replacement of the source
coordinates. Arbitrary existential auxiliary finite-tree variables are
allowed. Finite unions of these cells are the compilation class below.

**Theorem 8.2 (an acquired morphism graph has no finite ordinary compilation).**
The relation

$$
\mathcal G=\{(x,y)\in\mathcal T^2:x=\rho(y)\}
\tag{ARH.8.2}
$$

is not a finite union of ordinary cells. Adding finite literal-history
conditions at fixed epochs to those cells does not change the conclusion.
It follows that a coordinate-preserving finite ordinary-cell normalization
cannot handle every actually acquired mixed-epoch input of Definition 1.2.
This is a representation obstruction, not an undecidability assertion.

Proof. Suppose a finite union equals $\mathcal G$. Every nonempty disjunct
is then contained in $\mathcal G$. Apply the ordinary finite-term
unification supplied in [SLH, Theorem 74.4, proof (ii)][SLH] to that
disjunct's equations. This application involves only free terms, so
occurs-check and the full solved-substitution correspondence apply.
Discard inconsistent disjuncts. In a nonempty one, the solved substitution
expresses

$$
x=A(\mathbf z),\qquad y=B(\mathbf z)
\tag{ARH.8.3}
$$

in the remaining free variables, subject only to finitely many residual
ordinary disequalities. This includes originally existential variables
and any free coordinate left by the substitution.

Fix a satisfying assignment. Suppose a variable $z$ occurs in $B$.
Hold all other variables at their assigned finite trees. By the
one-variable fact in [SLH, Theorem 74.4, proof (ii)][SLH], each remaining
disequality, being true at the fixed assignment, excludes at most one
replacement value for $z$. Thus all but finitely many finite trees can
replace $z$ while staying in this same disjunct.

Let $a\ge0,b>0$ count occurrences of $z$ in $A,B$. Let $w_j$ be any fixed
choice of a tree with exactly $j$ leaves all labeled $\alpha$, for each
$j\ge1$. Infinitely many of these pairwise distinct trees avoid the
finite excluded set. With all other variables fixed, write $c_\alpha,
c_\beta,d_\alpha,d_\beta$ for their constant contributions to the two
leaf counts. Then

$$
\begin{aligned}
\#_\alpha A(w_j)&=aj+c_\alpha,&
\#_\beta A(w_j)&=c_\beta,\\
\#_\alpha\rho(B(w_j))&=d_\beta,&
\#_\beta\rho(B(w_j))&=bj+d_\alpha+d_\beta.
\end{aligned}
\tag{ARH.8.4}
$$

The second line uses exactly the actual images of $\alpha,\beta$ in
(ARH.1.1). Containment in $\mathcal G$ requires equality of both counts
for unbounded $j$. The alpha equality forces $a=0$; the beta equality
then, and in fact already, contradicts $b>0$. Hence $B$ contains no free
variable. This disjunct fixes one $y$, and containment in $\mathcal G$
fixes $x=\rho(y)$ as well. Each nonempty disjunct contains just one pair,
whereas $\mathcal G$ has infinitely many. This is the contradiction.

For the literal extension, physical-address locality (SLH.74.7) makes
every fixed finite history depend on a finite original prefix in its
source coordinates. Enumerate the finitely many such prefix patterns.
Each is described by ordinary equations with fresh frontier variables;
the literal outcomes are constant on a pattern. Distribute this finite
disjunction into (ARH.8.1). The result is still a finite union of ordinary
cells, already excluded. A fixed old row likewise has the ordinary
context-filling equations and all its class disequalities (ARH.1.2).

To exhibit the graph as an actual input, take

$$
P=\{L,R\},\quad C=\langle\square_1,\square_2\rangle,
\quad\pi=\{\{1\},\{2\}\},\quad H_0=\varnothing,
\quad H_{\rm rel}=\{(0,L,1,R,=)\}.
\tag{ARH.8.5}
$$

Writing the original tree $\langle x,y\rangle$, this record says exactly
$x=\rho(y)$. The old inequality adds no restriction, since
$\kappa(\rho(y))=\kappa(y)+1$ implies $\rho(y)\ne y$. Both endpoints
are original and reached. Proposition 2.1 acquires them by paid traversal,
one actual update, finite comparison and the complete cut. Its entire
fiber is therefore $\{\langle\rho(y),y\rangle:y\in\mathcal T\}$.
An ordinary description of this original-source fiber would give an
ordinary description of $\mathcal G$ by substituting
$u=\langle x,y\rangle$. It is impossible by the preceding proof. $\square$

The theorem rules out a route that simply turns all morphic constraints
into finitely many ordinary cells and then invokes the unchanged ground
binding test of [SLH, §74][SLH]. It does not exclude a finite description
which retains $\rho$, a richer automaton with a proved correspondence,
or another effective representation. It says nothing against a particular
constant recut on (ARH.8.5); for instance its $Q=P$ row is already retained.

**Theorem 8.3 (infinite orbit fibers cannot be exact finite old-input unions).**
Let $\mathcal O=\{T_k:k\ge0\}$. Every basic old-row/literal-history fiber
$\mathcal U_{R'}(H')$ contained in $\mathcal O$ is finite, allowing its
own arbitrary finite original cut $P'$. Hence no infinite fiber in
Theorem 5.2 with $\tau=1$ is a finite union of such basic fibers.

Proof. Use the exact finite prefix decomposition [SLH, Definition 74.2
and (SLH.74.8)][SLH] for $R',H'$. If this basic fiber were infinite,
some nonempty cell would have a residual variable $x$ occurring in its
source term $W$. Otherwise each of finitely many ground cells would give
only one source. The only remaining constraints in a cell are its full
finite old disequality list $\Delta$; its literal replies are already
fixed by the prefix.

Fix one feasible valuation and every variable except $x$. The supplied
one-variable free-term fact again says that each true disequality excludes
at most one new value of $x$. Let $F$ be their finite union of excluded
values. Choose an integer $M\ge2$ with $2^M>|F|+1$, fix a full binary
shape with $M$ leaves, and vary its two leaf labels. At least two distinct
such trees $z,z'$ avoid $F$. Their substitutions into $W$ yield different
original sources: at an occurrence of $x$ their entire subtrees differ.
Both substitutions preserve the old row, every old inequality and all
literal replies. Their total leaf counts are the same,

$$
A+cM\ge2,
\tag{ARH.8.6}
$$

where $c\ge1$ is the number of occurrences of $x$ in $W$ and $A\ge0$
is the fixed contribution from the rest of $W$.

By (ARH.4.2), the leaf counts of $T_0,T_1$ are one, and
$\ell(T_{j+2})=\ell(T_{j+1})+\ell(T_j)$. They are strictly increasing
from $T_2$ onward. There is at most one orbit tree of each leaf count
at least two. The two distinct legal substitutions with (ARH.8.6) cannot
both lie in $\mathcal O$, contradicting containment. Thus every such
basic fiber is finite, and a finite union cannot equal an infinite
subset of $\mathcal O$. $\square$

Both representation obstructions have a paid-interface consequence.
Suppose a deterministic source-total converter with a common $K$ new
reads outputs only an ordinary finite description in the same original
coordinates, or only a basic old-row/literal input, and promises that each
terminal description's full semantic fiber over **all** $\mathcal T$
is exactly its incoming branch fiber. Assume no relation, morphic domain
promise or other source-bearing information survives outside that
description. The finite reply-tree supply in §2 gives only finitely many
terminal descriptions, even with serial updates. Their fibers cover the
incoming domain and are contained in it. For (ARH.8.5) this contradicts
Theorem 8.2; for an infinite orbit fiber and basic outputs it contradicts
Theorem 8.3.

The requirement “over all $\mathcal T$” is essential. Describing a branch
as a basic fiber *intersected with the retained morphic promise* is a
richer representation, not the forbidden conversion. Unbounded paid
acquisition of the actual tree and task-specific output of a constant
row are also not excluded. Theorem 8.3 shows why the infinite-tail
consumer of Theorem 6.1 is not merely a finite exact selection of already
solved literal-history inputs.

## 9. Mathematical scope, suppliers and remaining obligations

**Definition 9.1 (the unresolved unrestricted decision).** For arbitrary
finite $R,H_0,H_{\rm rel},Q$ satisfying Assumption 1.3, the unrestricted
question remains an effective exact decision of
$\exists h\,\operatorname{PrefDet}(U,Q,h)$, together with a paid
source-total full-row consumer in the positive case, or an exact negative
theorem covering the proposed unrestricted input class. In the guarded
representation of Proposition 3.2 this requires reasoning about all
joint finite-tree solutions of the coupled signed morphic equations,
including concrete outside variation and every target subtree comparison.

Decidable membership of a single concrete tree, ordinary unification of
the same-epoch part, an emptiness result for another constraint language,
or a search that terminates only after a suitable prefix bound is supplied
does not settle this question. Theorem 8.2 rules out one finite ordinary
compilation; it does not prove the unrestricted question undecidable.
Theorem 6.1 decides the recognized root-certificate fragment with arbitrary
additional histories, without claiming that the fragment exhausts all
solvable inputs. Equation (ARH.2.3) already establishes static/serial
**existence** equivalence under the stated contract; general minimum raw
budgets and equality of those minima remain unresolved. Proposition 7.1
settles its own one-read example only.

The source-relative additions are the paid signed-history and guarded
endpoint correspondences, the root-certificate interface to the supplied
stability classification, the exact finite/cofinite full retained fiber,
its complete-row decision and consumer, and the two precise representation
obstructions. These are `repo-derived` ordinary mathematical deductions.
The atomic orbit classification, historical decoder, template certificates,
Hall matching, finite-term unification and finite-transcript method are
reused suppliers. No global priority claim is made.

The relevant supplier boundaries are as follows, attached to the
correspondences they support.

- [SLH, §§59–62][SLH] supply actual old-row acquisition, full class
  inequalities, local transport and complete-state continuation. [SLH,
  §§29, 55, 69 and 74–75][SLH] supply guarded literal semantics, delayed
  templates, finite historical VALUE minimax, and the general literal-only
  full-row criterion. [SLH, §§70–73][SLH] keep their exact multi-hole
  ancestor and joint-extension conditions. None is replaced by a renamed
  ground-binding algorithm here.
- [CENTRALIZER][CENTRALIZER] supplies (ARH.4.4), with the exact source
  identification in Definition 4.1. [TRANSPORT][TRANSPORT] supplies the
  actual image parser, injectivity, original-address transport, clock and
  guarded atomic subtree formulas. Their uses here are ordinary theorem
  applications; they do not by themselves supply an acquired mixed-history
  decision or certify a physical cut.
- [ActualTreeReadoutAcquisition][ACQUISITION], `source_foundation` and
  `acquisition_foundation`, supplies the existing leaf-rigidity and finite
  traversal correspondence consumed through [SLH, §§53, 55 and 59][SLH].
  Its original static Boolean policy is not a serial full-row service.
  The finite-record/counting and realized-image factor suppliers named in
  [SLH, §75][SLH] likewise retain their own hypotheses; finite image alone
  does not ensure bounded observation, as Proposition 7.1 without its
  relation demonstrates.
- Finite free-term unification is `literature-attested` by
  [Martelli–Montanari, *An Efficient Unification Algorithm*, ACM TOPLAS
  4(2), 258–282][MM]. The exact finite occurs-check and solved-substitution
  argument used here is already supplied in [SLH, §74, proof (ii)][SLH].
  It is applied only to ordinary free terms in Theorems 8.2–8.3.
- [Hall, *On Representatives of Subsets*][HALL] and the pinned mathlib
  [`Finset.all_card_le_biUnion_card_iff_existsInjective'`][MATHHALL]
  supply the finite matching step used by [SLH, §61][SLH]. Its finite
  index set is the old class set, and values are finite trees with
  decidable equality. [Pinned `FirstOrder.Language.Term` and
  `Term.subst`][SYNTAX] supply syntax and substitution, not a solver
  for interpreted $\rho$ constraints. These library statements do not
  establish an unproved mixed-epoch correspondence.
- [Comon et al., *Tree Automata Techniques and Applications*, §1.4][TATA]
  is the `literature-attested` tree-homomorphism background: (ARH.1.1)
  is a fixed nondeleting linear ranked homomorphism. Injectivity here
  comes from the specific parser, not from linearity. Ordinary image
  or preimage language closure does not compare two coupled unknown
  mixed-epoch endpoint trees.
- [Barguñó–Creus–Godoy–Jacquemard–Vacher, *Decidable Classes of Tree
  Automata Mixing Local and Global Constraints Modulo Flat Theories*,
  LMCS 9(2:1)][TABG] supplies decidable emptiness in its stated automaton
  language. Its fixed old-hole use is already supplied in [SLH, §61][SLH].
  No representation of arbitrary coupled $\rho$ constraints in that
  language, nor a decision of (ARH.2.2), follows merely from this citation.
- [Marshall–Meadows–Narendran, *On Unification Modulo One-Sided
  Distributivity: Algorithms, Variants and Asymmetry*, LMCS 11(2:11)][OSD]
  studies a different specified equational theory. Its homomorphism
  methods are a possible comparison, but no transfer to the fixed two
  leaf images, finite original ground sources, signed guards and full-row
  boundedness problem is asserted. No complexity claim is imported.

**Definition 9.2 (retained stochastic and further deterministic questions).**
The original fixed-prior stochastic $j_c$ zero/positive alternative,
joint full-law calibration, finite exact stochastic optimum, and
effective charged stochastic attainment keep their original standards.
[Fixed full-residual null, Theorem 4.1 and Corollary 5.2][NULL] excludes
the specified 155-coefficient separator family. Its full-marginal and
omitted-residual distinctions prevent either $j_c=0$ or $j_c>0$ from
following. None of the deterministic rows in this volume supplies a
compatible full-law pair, a stochastic optimum, or an exact paid sampler.
The finite/cofinite orbit index description is not a stochastic
finite-law replacement.

For the unrestricted deterministic question, epoch-potential methods for
coupled records and the separate full three-hole root-record family remain
candidate increments. No classification of either is assumed here and
neither substitutes for Definition 9.1. A partial solution on the present
recognized fragment does not complete the persistent self-calibration
programme.

[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[TRANSPORT]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[CENTRALIZER]: ../../../D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.lean
[ACQUISITION]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[MM]: https://doi.org/10.1145/357162.357169
[HALL]: https://doi.org/10.1112/jlms/s1-10.37.26
[MATHHALL]: https://cdn.jsdelivr.net/gh/leanprover-community/mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Combinatorics/Hall/Finite.lean
[SYNTAX]: https://cdn.jsdelivr.net/gh/leanprover-community/mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/ModelTheory/Syntax.lean
[TATA]: https://inria.hal.science/hal-03367725/document
[TABG]: https://arxiv.org/abs/1302.6960v2
[OSD]: https://arxiv.org/abs/1503.06687v2
[NULL]: RECURSIVE_RELATIONAL_OBSERVATION_FIXED_FULL_RESIDUAL_NULL.md

## 追加锚（本行以下为增补区）

## 10. A decidable synchronous family of complete acquired inputs

This extension decides the entire-row question of Definition 9.1 on a
recognizable family of coupled histories. It keeps the original source,
original cuts, full old row, endpoint guards and paid contract of §1.
Sections 2–3 supply the original-prefix/service bridge and the guarded
source representation. Sections 4–8 keep their own orbit and representation
results; none is a new conclusion of this extension. The new decision
uses a relation of **complete-row disagreement** on exact feasible tuples.
It does not use finite source samples or assume independent coordinates.

**Definition 10.1 (fixed normalization and comparison test).** Use exactly
$d$, the depth-$d$ patterns, variables $X_\eta$, source terms $W_\eta$,
old inequalities $\Delta_\eta$, and guarded endpoints of Definition 3.1
and Proposition 3.2. In particular, patterns record replies at depths
strictly less than $d$, and a reached depth-$d$ frontier is an arbitrary
nonempty finite subtree. Different old classes have different variable
names; every occurrence of one class uses the same names.

For each guarded endpoint, distribute its interpreted iterate through
all explicit pairing nodes and expand its concrete leaves. The result
has syntax

$$
S::=\alpha\mid\beta\mid\langle S,S\rangle\mid[a,x],
\qquad [a,x][v]:=\rho^a(v(x)),\quad a\in\mathbb N.
\tag{ARH.10.1}
$$

The decoration is an interpreted function, not a free constructor.
Ordinary variables are $[0,x]$. Expanding any ground part is effective
and finite; no bound on the size of that expansion is asserted.

Define a deterministic partial comparison compiler $\mathsf{Eq}(S,T)$.
It returns a finite Boolean formula, or the token $\mathsf{unsupported}$.
Use the following priority order, with the symmetric cases included.

1. Syntactically identical expressions give true. If both expressions
   are ground, evaluate them as finite trees and return their equality.
2. Two decorated variables give the atom
   $\rho^a(x)=\rho^b(y)$. A decorated variable and a ground expression
   $g$ give the atom $\rho^a(x)=g$.
3. Two explicit pairs give the conjunction of their child comparisons,
   provided **both** child comparisons compile. Different explicit root
   constructors give false. This includes a leaf against an explicit pair.
4. A decorated variable against a nonground explicit pair is unsupported.

These cases are exhaustive after symmetry. Ground against a nonground
pair is handled by constructor comparison, not rejected. The recursion
terminates by syntax size. A failed child is not suppressed because the
other child returned false. A signed disequality is the negation of the
**whole** compiled equality; it is not the conjunction of child
disequalities. In particular, the test performs no ordinary unification
and makes no assumption that an unsupported equality is false.

**Definition 10.2 (eligibility order).** The family $\mathfrak S$ consists
of the complete input presentations $(P,Q,R,H_0,H_{\rm rel})$ passing the
following finite procedure. Its service theorem additionally requires
the actual acquisition and nonempty-fiber hypotheses of Assumption 1.3.

First enumerate the prefix cells of Proposition 3.2 and reject those
violating any literal or either endpoint-existence guard. On **every**
remaining cell require compilation of every old class inequality and
every signed retained relation. If any compilation is unsupported, the
input is outside $\mathfrak S$. Write $D_\eta$ for the conjunction of the
compiled conditions, retaining all off-task old inequalities. Lemma 11.2
below constructs its exact finite-tree automaton and decides emptiness.
Discard exactly the cells with no satisfying assignment.

Only then compute $J_\eta,E_\eta,A_{\eta,q}$ from (ARH.3.4) on each
nonempty cell, and require compilation of every equality
$A_{\eta,q}=A_{\eta,r}$ for distinct $q,r\in J_\eta$ at epoch zero.
Denote the resulting formula by $e_{\eta,qr}$. A failure here also means
outside $\mathfrak S$. No test is needed for the outside term itself:
its complete variable values will be included in the disagreement relation.

For $X_\eta=\varnothing$, evaluate all constraints directly on the single
empty assignment. A surviving such cell is one ground source and needs
no tuple automaton. Its target comparisons are ground and compile.
Thus zero old holes, ground cells, empty cuts and root cuts are included.

This definition chooses constraint eligibility **before** emptiness, and
target eligibility **after** exact emptiness. Requiring target eligibility
also on empty cells, or first solving contextual equations by substitution,
would define different procedures. No equivalence of those families is
claimed. The two algorithms in §11 have no dependence on this definition,
so the eligibility procedure is terminating rather than circular.

**Proposition 10.3 (the whole-source correspondence used by the compiler).**
For an input passing the constraint stage, including all its empty cells,

$$
\coprod_\eta\{v:X_\eta\to\mathcal T:D_\eta(v)\}
 \ \longrightarrow\ U,\qquad (\eta,v)\longmapsto W_\eta[v]
\tag{ARH.10.2}
$$

is a bijection. Here $U$ is the entire fiber (ARH.1.4). The syntactic
comparison test gives equivalent predicates and does not change that
fiber. The feasible tuple set may be arbitrarily coupled.

Proof. Proposition 3.2 already gives the guarded correspondence. To check
its interface, take a source with old row $R$. Its old class values are
unique, satisfy every distinct-class inequality, and have unique original
prefix patterns and frontier subtrees. These recover $\eta,v$; repeated
old occurrences recover the same subtrees. Conversely filling those
patterns subject to all old inequalities gives exactly the old outside,
reached holes and complete partition. Each variable has an occurrence
at $a_bs$, where $a_b$ is a chosen reached old representative and $|s|=d$.
Reading that mathematical subtree recovers its valuation, proving
injectivity as well as surjectivity.

Every variable occurrence is deeper than every literal, relation endpoint
and new cut address. Navigation to a recorded endpoint either reaches an
original symbolic subtree, or first encounters a known original leaf.
In the latter case the remaining navigation takes place in the known
finite image of that leaf. It decides existence at the recorded epoch;
absence falsifies either signed record. In the former case the endpoint
is the iterate of the whole original subtree. Thus normalization (ARH.10.1)
evaluates to the actual entire endpoint, including born endpoints. Literal
repetitions and absent replies remain their exact constant cell conditions.

Each successful comparison step is an equivalence: identity, ground
computation, an unchanged interpreted atom, free-pair cancellation, or
a clash of explicit constructors. Boolean negation preserves that
equivalence. Induction through the comparisons therefore replaces every
predicate by an equivalent one on the same valuations. The conjunction
includes every old inequality and every acquired record. This proves
(ARH.10.2) in both directions. Empty-cell removal deletes no source.

The representation consumes the producer/access-cut correspondence of
Proposition 2.1. For a fixed record schedule, that producer actually pays
for the old row and endpoint traversals at their epochs, keeps the acquired
descriptions until comparison is possible, and then cuts access to all
unstated source-bearing state. Every satisfying source produces the same
retained input, and every source producing it satisfies these predicates.
This supplies admissibility of the examples below, not a free endpoint
comparison port. Acquisition costs can vary without bound across finite
sources. An adaptive producer still owes the full-state correspondence
of Assumption 1.3. $\square$

## 11. Exact finite-tree automata for aligned morphic relations

**Definition 11.1 (padded tuple representation).** For $k\ge1$, let the
finite ranked alphabet $\Sigma_k$ consist of vectors in
$\{\alpha,\beta,\mathsf{branch},\bot\}^k$ other than the all-$\bot$
vector. A vector has rank two if some coordinate is branch, and rank
zero otherwise. The symbol $\bot$ represents an absent coordinate.
The convolution $\operatorname{conv}(t_1,\ldots,t_k)$ has domain the union
of the finite coordinate domains and carries their reply vector at each
node. This union is a finite full binary domain, so it is a
$\Sigma_k$-term.

A valid whole-tuple term has no $\bot$ at its root. At any binary node,
a branch coordinate has nonabsent labels at both children; a leaf or
absent coordinate has $\bot$ at both children. At a nullary node no
coordinate is branch. These local rules imply that a coordinate never
reappears below its leaf or absence. Denote the resulting language by
$V_k$. Internal subterms may have absent root coordinates, even though
roots of $V_k$ do not. No node with all coordinates absent is inserted.

These rules are an effective finite-state check: a bottom-up state can
store the root vector and a validity flag, check the two child vectors,
and impose the nonabsent-root condition only at acceptance. Restricting
a valid term to each coordinate recovers a nonempty finite tree. The
rules and the exclusion of all-absent nodes show that its domain is
exactly the union of those recovered domains. Consequently convolution
and coordinate recovery are inverse bijections between $\mathcal T^k$
and $V_k$. Padding is determined by the coordinate trees, not chosen
auxiliary information. Zero-coordinate cells use the convention of
Definition 10.2 instead of an empty convolution tree.

**Lemma 11.2 (exact primitive relations, Boolean closure and witnesses).**
On any fixed finite list of nonempty finite-tree coordinates, the
relations

$$
\rho^a(x)=\rho^b(y),\qquad \rho^a(x)=g
\tag{ARH.11.1}
$$

have effectively constructible finite bottom-up tree automata on valid
convolutions, for fixed $a,b\ge0$ and ground $g$. Coordinates $x,y$ may
be the same coordinate. Any finite Boolean combination of these atoms
has an exact such automaton. Its emptiness is decidable, and a nonempty
language has an effectively extractable finite tuple witness.

Proof. Use the image parser and injectivity already used in (ARH.3.5).
Their relevant algebra is short: no $\rho$-image has root $\alpha$;
the images of $\alpha$, $\beta$ and a pair are respectively $\beta$,
$\langle\beta,\alpha\rangle$ and a pair whose right child is itself an
image, hence not $\alpha$. These cases are disjoint, and the last case
recursively parses its children. This gives a unique partial inverse
on each finite ground tree and injectivity of every iterate. Cancel
$\min(a,b)$ in the first atom. It suffices to recognize
$y=\rho^e(x)$ for fixed $e\ge0$.

Here is a finite checking construction, including padding. Its main state
checks two selected coordinates at the current common suffix. If the
$x$ coordinate is branch, require branch in $y$ and the main state at
both children. If $x$ is the leaf $\lambda$, check the selected pair of
whole subtrees against the two fixed templates
$(\lambda,\rho^e\lambda)$. Template states are pairs of subtrees of these
fixed templates, also allowing an empty component. They check the current
selected labels and pass their child templates to the children. Once
both selected components are empty, a blank state requires both labels
to be $\bot$ and propagates itself wherever other coordinates continue.
If the selected components have ended but other coordinates give the
current convolution node rank two, the child states are also blank.
Thus all ranks and all deeper padding forced by other tracks are handled.

There are finitely many main, template and blank states. These top-down
rules can be read as a finite nondeterministic bottom-up transition
relation, with the main state required at the root. Intersect with $V_k$.
Induction on the finite $x$ tree proves that its successful run exists
exactly when the selected $y$ tree is $\rho^e(x)$: pairs use the two
induction hypotheses, and leaves use the complete fixed images. Blank
states add no selected-coordinate nodes. Reading one physical coordinate
for both selected tracks gives the same proof when $x=y$; it does not
make two independent copies of that coordinate's value.

For $\rho^a(x)=g$, apply the partial inverse $a$ times to $g$. If it
fails, the atom is false; otherwise it is exactly equality of $x$ to
one computed finite template. A template recognizer, with the same blank
handling for other coordinates, recognizes that condition.

For completeness, the finite automata operations used here are the
standard finite ranked-tree ones. Intersection takes products of states;
union takes disjoint runs; subset determinization assigns each subtree
the set of its possible old states. Include the empty subset to make the
transition function total. Complement swaps acceptance in that complete
deterministic automaton and is then intersected with $V_k$. This is
complement relative to valid **finite** tuples. Induction on a Boolean
formula gives its exact language, including negated conjunctions and
repeated coordinates.

For emptiness, start with states reached by nullary transitions and
repeatedly add targets of binary transitions whose children were already
added. The finite state set makes this terminate. Structural induction
shows that the final set consists exactly of states reached by finite
terms. Store the first producing transition for each new state; its
children were produced earlier, so this record unfolds into a finite
witness. An accepting productive state is therefore equivalent to a
nonempty language and supplies a genuine finite tuple by Definition 11.1.
These are mature automata constructions [TATA, Theorems 1.1.9, 1.3.1
and 1.7.4][TATA]; the argument specifies their exact hypotheses and
padding interface here. $\square$

Every compiled $D_\eta$ is consequently represented on the **joint**
coordinate tuple. Arbitrary finite networks of these compiled atoms,
including cycles, different epoch offsets and disequalities, require no
factorization of that tuple language. This is why recognizing the graph
of a fixed iterate is useful despite the ordinary-cell obstruction in §8.
It does not imply that all contextual comparisons are recognizable; §17
exhibits the precise missing closure.

## 12. The exact kernel of the entire original row

**Proposition 12.1 (one whole-row disagreement relation).** Let a nonempty
cell of an input in $\mathfrak S$ have $k=|X_\eta|\ge1$. Let
$O_\eta\subseteq X_\eta$ be the variables occurring in $E_\eta$ after
the original $Q$ holes have been removed. For two valuations $v,w$ put

$$
\begin{aligned}
\mathsf{Bad}_\eta(v,w):={}&D_\eta(v)\land D_\eta(w)\land\\
 &\left[
 \bigvee_{x\in O_\eta}v(x)\ne w(x)
 \ \lor\!
 \bigvee_{\{q,r\}\subseteq J_\eta}
       \bigl(e_{\eta,qr}(v)\mathbin{\mathsf{xor}}e_{\eta,qr}(w)\bigr)
 \right].
\end{aligned}
\tag{ARH.12.1}
$$

Empty disjunctions mean false. This relation has an effective finite
bottom-up automaton over $\Sigma_{2k}$, whose accepted terms are exactly

$$
\left\{\operatorname{conv}(v,w):
 W_\eta[v],W_\eta[w]\in U\text{ in cell }\eta,\quad
 R_Q(W_\eta[v])\ne R_Q(W_\eta[w])\right\}.
\tag{ARH.12.2}
$$

Here the two copies of $X_\eta$ are ordered alike. They are mathematical
coordinates for comparing possible sources, not two physical registers.

Proof. By Proposition 10.3 the first two conjuncts specify exactly both
feasible assignments, keeping every old and acquired constraint on each.
The reached set and numbering $J_\eta$ are fixed on this cell. Recutting
commutes with filling, since all residual occurrences are below the cut
addresses. Thus the concrete outside is exactly $E_\eta[v]$ or
$E_\eta[w]$, with the same fixed, numbered hole markers.

For a fixed free term with these hole markers, cancellation down to an
occurrence of each variable gives

$$
E_\eta[v]=E_\eta[w]
\quad\Longleftrightarrow\quad
\forall x\in O_\eta,\ v(x)=w(x).
\tag{ARH.12.3}
$$

The forward implication uses only variables that actually occur outside;
the reverse follows by substitution. A variable occurring both outside
and inside holes is still included once in $O_\eta$. Its repeated
occurrences need not be independent.

By (ARH.3.4) and compiler correctness, $e_{\eta,qr}(v)$ is exactly the
truth of complete subtree equality at those two original holes. Two
partitions of the same finite reached set coincide if and only if all
unordered distinct-pair equality truths coincide. Combining this fact
with (ARH.12.3) proves (ARH.12.1) equivalent to full-row disagreement.
In particular an unbounded outside tree is part of the predicate, not
replaced by the partition.

Lemma 11.2 recognizes both copies of $D_\eta$, each target formula and
cross-copy coordinate equality. Its blank-state construction permits the
other $2k-1$ or $2k-2$ coordinates to extend further than selected ones.
Boolean closure, intersected with $V_{2k}$, therefore constructs exactly
(ARH.12.2). For a zero-variable cell the row is constant and its bad
relation is empty, as already handled separately. $\square$

## 13. A terminating finite-prefix test with finite negative witnesses

**Theorem 13.1 (diagonal-prefix saturation).** Let $\mathcal A$ be any
finite bottom-up automaton over $\Sigma_{2k}$, with finite state set $S$
and final set $F$, accepting exactly a given relation of valid tuple pairs.
A symbol is diagonal if each coordinate in the first half equals the
corresponding coordinate in the second half, including $\bot$.
Compute the productive states $Z_0$ as in Lemma 11.2, and define

$$
\begin{aligned}
Z_{j+1}={}&\{s:\text{some diagonal nullary transition ends at }s\}\\
 &\cup\{s:\text{some diagonal binary transition }
                  a(s_L,s_R)\to s\text{ has }s_L,s_R\in Z_j\}.
\end{aligned}
\tag{ARH.13.1}
$$

This sequence decreases and reaches a fixed set $Z_\infty$ effectively.
There is a finite number $j$ of initial tuple levels on which no accepted
pair agrees if and only if $F\cap Z_\infty=\varnothing$.
An empty intersection yields such a computable $j$. A nonempty
intersection yields, for every requested $j$, an accepted pair of
**finite** tuples agreeing at every coordinate address of length $<j$.

Proof. For every $j\ge0$ and state $s$, the exact invariant is

$$
s\in Z_j\quad\Longleftrightarrow\quad
\text{some finite term has a run to }s
\text{ and every label at depth }<j\text{ is diagonal}.
\tag{ARH.13.2}
$$

At $j=0$ there is no label restriction, so this is productivity, including
its finite-witness direction. At $j+1$ a nullary root must be diagonal
and then has no children. A binary root must be diagonal and each child
must have the property at $j$. Both directions of the induction now
follow exactly from (ARH.13.1): combine two finite child witnesses to
obtain a finite parent, or decompose an existing run into its children.
It is immaterial whether the automaton is deterministic.

Any transition with productive children has a productive target, hence
$Z_1\subseteq Z_0$. The operator in (ARH.13.1) is monotone in its child
set, so induction gives $Z_{j+1}\subseteq Z_j$. There are at most $|S|$
strict decreases. Once two consecutive sets are equal, every later set
is equal; this gives a terminating test, with at most one additional
comparison to detect stabilization. Stored productive witnesses and the
induction also give an effective witness construction for any requested
finite $j$ and any state in $Z_j$.

For a valid tuple pair, diagonality through these $j$ levels is exactly
agreement of all paired coordinate replies at addresses of length $<j$.
Indeed every address present in either coordinate occurs in the union
domain. Equality of its labels includes presence versus absence. Addresses
outside the union have absence in both copies automatically. This proves
both directions even when some coordinates terminate early.

Consequently $F\cap Z_j$ is nonempty exactly when an accepted pair has
that prefix agreement. If the stable intersection is empty, a computed
stage has empty intersection and is a separating depth. If it is nonempty,
a stable accepting state lies in every $Z_j$; (ARH.13.2) produces a finite
accepted pair for each $j$. Witnesses may depend on $j$. No single infinite
tree, infinite run, compactness argument or changed source domain is used.
$\square$

The condition is about the accepting **root** states of the same exact
relation automaton. Productive internal states may encode partial padding
or unfinished checks; every accepted completion still satisfies $V_{2k}$
and all constraints. This avoids treating independently productive
coordinate marginals as a jointly feasible source pair.

## 14. Complete original-prefix decision and the paid row consumer

**Theorem 14.1 (complete decision on $\mathfrak S$).** Under Assumption
1.3, suppose the complete input is in $\mathfrak S$. On each nonempty
cell with variables, construct the automaton of Proposition 12.1 and
compute its $F_\eta\cap Z_{\eta,\infty}$. The following are equivalent:

1. Every one of those intersections is empty.
2. There exists one finite original depth $H$ satisfying
   $\operatorname{PrefDet}(U,Q,H)$ on the entire $U$.
3. At the certified $N$, a deterministic effective source-total static
   service outputs the entire original $R_Q$ with a uniform finite
   new-read budget.
4. Such a service exists allowing paid real serial $\mathsf{ApplyRho}$
   on the same register.

The first condition is decidable. On a yes answer the procedure computes
$H$ and a legal static consumer. On a no answer it computes, for any
requested original depth $h$, two finite sources in the entire retained
fiber agreeing through depth $h$ and having different complete original
rows. No minimum-budget or uniform local-work bound is asserted.

Proof. All pattern lists and comparison tests are finite. Lemma 11.2
supplies exact feasibility and finite automata, and Theorem 13.1 supplies
a terminating test on each. Thus condition 1 is effective. Nonempty $U$
guarantees at least one nonempty cell; zero-variable cells always pass.

Suppose condition 1 holds. For each cell with variables choose a computed
$j_\eta\ge0$ with $F_\eta\cap Z_{\eta,j_\eta}=\varnothing$; choose
$j_\eta=0$ for a ground cell. Let $a_b$ be the original representative
of old class $b$ and put

$$
A=d+\max\bigl(\{0\}\cup\{|a_b|:b\in\mathcal B\}\bigr),
\qquad H=A+\max_\eta j_\eta.
\tag{ARH.14.1}
$$

This is a deliberately sufficient bound. If two sources in $U$ agree
at all original addresses of length at most $H$, their old class replies
at $a_bs$, $|s|<d$, give the same pattern tuple $\eta$. Every residual
variable has an original representative occurrence $a_bs_x$, $|s_x|=d$,
of length at most $A$. The two sources therefore agree on that variable's
replies at all relative lengths $<j_\eta$. Theorem 13.1 excludes
$\mathsf{Bad}_\eta$ for these two feasible tuples. Proposition 12.1
says that their **entire** rows coincide. This proves condition 2 across
all cells, not just separately inside a selected cell. Different cells
are distinguished by the same bounded original prefix.

If condition 1 fails, choose its failing nonempty cell. For any $h\ge0$,
use Theorem 13.1 with $j=h+1$ to construct two finite feasible tuples
$v,w$ agreeing at every relative address of length at most $h$ but
satisfying $\mathsf{Bad}_\eta$. Filling the fixed $W_\eta$ preserves
agreement through original depth $h$: an address either remains in its
fixed constructors or enters a variable at some nonnegative prefix
length and uses a relative suffix no longer than $h$. This includes
absence below leaves. Proposition 10.3 places both filled sources in
the entire actual $U$, and Proposition 12.1 gives their different full
rows. They disprove condition 2 at that $h$. Witness extraction is a
finite recursion of prescribed depth from stored productive completions;
it is an algorithm on finite objects for each requested $h$.

For $2\Rightarrow3$, use the already supplied decoder [SLH, Theorem
2.2][SLH], exactly as in §2. At the actual static epoch $N$, acquire enough
current raw replies to recover every original reply at $|s|\le H$.
A sufficient uniform count and address-length bound are

$$
K=2(2^{H+1}-1),\qquad
\max |p_{\rm physical}|\le H+\lceil N/2\rceil.
\tag{ARH.14.2}
$$

Repeated physical calls may be made and paid; deduplication is optional.
The finite recovered original prefix is a decoded mathematical value.
The newly acquired raw evidence is only the actual $N$-epoch address/reply
list, not invented epoch-zero acquisition events.

Enumerate all finite original trees by size and encoding. For each,
compute its old row, all stipulated literals, both endpoint guards and
all complete signed comparisons, and test its agreement with the decoded
prefix. These are decidable finite computations. The actual unknown
source is one enumerated candidate satisfying all tests, so this local
search terminates on every actual run. Compute the entire $R_Q$ of the
first passing witness, including its concrete outside, reached original
holes in order and full equality partition. Condition 2 proves this is
the actual required row. The witness is used to compute a value already
proved common to the conditioned fiber; it is not declared to be the
actual source. An automaton witness after intersection with the decoded
prefix gives another implementation, but is unnecessary for this consumer.

The implication $3\Rightarrow4$ is service-class inclusion. For
$4\Rightarrow2$, reuse the verified operational bridge (ARH.2.3), whose
needed hypotheses do not concern the syntax of $D_\eta$. To make the
interface explicit, a deterministic source-total $K$-read service has
finitely many reachable four-valued reply prefixes. At each such prefix,
its computation and real updates before its next read or output are
fixed by common state and those replies, and are finite by source-totality.
Therefore the addresses submitted anywhere in this finite reply tree
have some finite maximum length $h$. The original-address locality
(SLH.74.7) says that a physical reply at any epoch and address $p$ depends
only on the original prefix through $|p|$. Equal original $h$-prefixes
force identical serial replies, updates and output by induction along
the service. Correctness gives condition 2. This uses no reset, reroot,
clone, identity port or observable update timing; those are excluded by
Assumption 1.3. It neither extracts $h$ from arbitrary code nor compares
the minimum static and serial budgets.

All computations described above terminate on their stated domains.
The computed $H$ and sufficient raw bound are independent of the allowed
$N$; decoder addresses depend on $N$. Historical acquisition, certification,
entry, installation, automaton construction, finite-tree enumeration,
address formation and lengths, working memory, retention, actual updates,
archives and the complete output remain separately charged. The consumer
makes no new update and no unknown-tree equality query. Outputting a new
row does not remove any accessible history; a later cut needs its own
complete-state correspondence. $\square$

For a presentation outside $\mathfrak S$, the procedure returns
$\mathsf{outside\ family}$ before applying this yes/no test. That result
is neither a negative service decision nor an emptiness decision for
arbitrary coupled morphic constraints. The unrestricted question in
Definition 9.1 is preserved.

## 15. A broad family included without a semantic eligibility oracle

**Proposition 15.1 (equal-level cuts and within-record aligned endpoints).**
Every admissible input with the following syntactic properties belongs
to $\mathfrak S$: $P$ is any subset of one original address level,
$Q$ is any subset of another original address level, and the two endpoint
addresses of each relation record have equal lengths. The two levels
may differ; different records may use different lengths and arbitrary,
possibly unequal, certified epochs. Literal histories, repeated old
classes, off-task classes, missing cuts, signs and coupling patterns are
unrestricted. Empty subsets and the root level are included.

Proof. Let the old cut level be $a$. All residual variable occurrences
in $W_\eta$ have absolute depth $a+d$, even when an old class is repeated.
A normalized endpoint at address length $s$ therefore has every nonground
decorated variable at relative depth $a+d-s$. Expansion of a known
original leaf contributes only ground subtrees; it does not shift a
variable occurrence.

In a comparison of endpoints of equal address length, both expressions
have their nonground frontier atoms at this same relative depth. Above
it a nonground expression has an explicit pair root. At it a nonground
expression is a decorated variable. Hence a decorated variable can face
only another decorated variable or a ground subtree, never a nonground
pair. Ground comparisons and constructor clashes already compile. This
proves compilation of every relation record after its guards, for all
patterns, whether or not their constraints are feasible. Old class
comparisons have common frontier depth $d$ and obey the same argument.
For target holes on one level, the argument applies with epoch zero and
common relative frontier depth $a+d-|q|$. Thus their comparisons also
compile. If there are no reached old holes there are no variables and
the assertion follows from the ground convention. The same reasoning
covers empty $Q$, absent endpoints filtered by their guards, and root
cuts. This proves the stated entire-input inclusion. $\square$

No completeness of either cut is required. In particular, unknown
concrete outside subtrees can remain; Theorem 14.1 decides their effect
through (ARH.12.1). The proposition does not authorize moving an original
cut to a convenient level. The larger tested family also includes the
non-level positive recut in the next section.

## 16. Coupled non-orbit examples with complete positive and negative outputs

**Proposition 16.1 (an active one-read full-row consumer).** Take four
original old holes and four distinct old classes:

$$
\begin{gathered}
P=\{LL,LR,RL,RR\},\quad
C=\langle\langle\square_1,\square_2\rangle,
          \langle\square_3,\square_4\rangle\rangle,\quad
\pi=\{\{1\},\{2\},\{3\},\{4\}\},\\
H_0=\{(0,LRL,\mathsf{absent}),(0,RR,\mathsf{branch})\},\\
H_{\rm rel}=\{(0,LL,1,LR,=),\ (0,RL,1,RR,=),\
                       (2,LL,0,RL,\ne)\},\\
Q=\{LLL,LLR,RL,RR\},\qquad N\ge2.
\end{gathered}
\tag{ARH.16.1}
$$

This input belongs to $\mathfrak S$ and has entire fiber

$$
\begin{aligned}
\{u_{b,t}:={}&\langle\langle\rho(b),b\rangle,
                       \langle\rho(t),t\rangle\rangle:\
 &b\in\{\alpha,\beta\},\quad t\text{ is a finite branch tree},\\
 &\rho(b),b,\rho(t),t\text{ are pairwise distinct},\quad
                     t\ne\rho^2(b)\}.
\end{aligned}
\tag{ARH.16.2}
$$

Its whole original target has exactly the following two rows:

$$
\begin{array}{c|c|c|c}
b&\text{reached cuts}&\text{outside context}&\text{partition}\\
\hline
\alpha&RL,RR&
\langle\langle\beta,\alpha\rangle,
                 \langle\square_1,\square_2\rangle\rangle&
\{\{1\},\{2\}\}\\
\beta&LLL,LLR,RL,RR&
\langle\langle\langle\square_1,\square_2\rangle,\beta\rangle,
                 \langle\square_3,\square_4\rangle\rangle&
\{\{1\},\{2\},\{3\},\{4\}\}.
\end{array}
\tag{ARH.16.3}
$$

For each allowed $N$, the minimum new-read count in both service classes
is one for this example.

Proof. Write the old values at $LL,LR,RL,RR$ as $x,b,z,t$. All four
positions are reached. The absent reply at $LRL$ makes $b$ a leaf; the
reply at $RR$ makes $t$ a branch. The two positive records say exactly
$x=\rho(b)$ and $z=\rho(t)$. The negative one says
$\rho^2(x)\ne z$, equivalently $\rho^3(b)\ne\rho(t)$, and injectivity
gives $t\ne\rho^2(b)$. Retain the six old inequalities explicitly.
Every implication reverses, proving (ARH.16.2) on all finite sources.
Taking $t=\langle\alpha,\alpha\rangle$ makes both leaf choices legal.
For each choice infinitely many other branch trees remain legal.

If $b=\alpha$, then $LL$ contains the original leaf $\beta$; neither
$LLL$ nor $LLR$ is reached. The retained old inequality between $RL,RR$
gives the first complete row. If $b=\beta$, then $LL$ contains
$\langle\beta,\alpha\rangle$; its two new holes have those different
leaf values. The other two holes contain $\rho(t),t$, both branch trees,
which are distinct by the old row. They therefore differ from both leaf
holes. This proves every entry of the second complete row, including all
cross-parent comparisons and the concrete outside leaf $b$.

For eligibility, $P$ is level two and every relation has level-two
endpoints, so the constraint-stage part of Proposition 15.1 applies
regardless of $Q$. Here $d=4$. In a nonempty cell, the literal forces the
entire $b$ pattern to be a concrete leaf, and the first equality forces
the entire $x$ pattern to be the corresponding ground tree $\rho(b)$.
A pattern with a depth-four frontier cannot fill to such a small tree.
Consequently any reached $LLL,LLR$ target is ground. The other two target
terms have equal relative frontier depth $d$, so they compare successfully
with each other; ground-versus-term comparisons also compile. Exact empty
cell removal before target eligibility is used here. Thus the non-level
$Q$ is admitted without changing it.

Since $LR$ is a known reached original hole, its current subtree is
$\rho^N(b)$. Apply the **root** case of [SLH, Theorem 2.2][SLH] under that
physical prefix: read just

$$
LR\,R^{\lceil N/2\rceil}.
\tag{ARH.16.4}
$$

For even $N$, the replies $\alpha,\beta$ select $b=\alpha,\beta$.
For odd $N$, absent and $\alpha$ respectively select those two cases.
This is the supplied leaf/root decoder; no new hole comparison is made.
Return the entire corresponding row (ARH.16.3). The address length is
$2+\lceil N/2\rceil$ and remains paid. Both rows occur at a common
retained input, so a zero-read deterministic service, even with real
unobserved updates, cannot choose correctly. This proves the
example-specific minimum.

The family is not a product: $t=T_3$ is legal for $b=\alpha$ and excluded
by $t\ne\rho^2(b)$ for $b=\beta$, whereas
$t=\langle\alpha,\alpha\rangle$ is legal for both. It is not restricted
to one whole-source atomic orbit. For example, the latter $t$ gives a
source not equal to any $T_j$: its left subtree is $T_2$ when $b=\alpha$
and $T_3$ when $b=\beta$, which would force the right subtree to be $T_1$
or $T_2$ respectively in an orbit source. The actual right subtree is
$\langle\rho(t),t\rangle$ and fails either forced equality.

Proposition 2.1 supplies a legal finite paid producer at epochs zero,
one and two, retaining earlier endpoint descriptions until comparison
and cutting all extra source-bearing fields afterwards. Thus the small
retained record really has (ARH.16.2) as its whole fiber under the contract.
The one-read claim concerns only subsequent new reads. $\square$

**Proposition 16.2 (a coupled chain with no uniform full-row budget).**
Keep $P,C,\pi$ from (ARH.16.1), but now take

$$
\begin{gathered}
H_0=\{(0,LL,\mathsf{branch}),(0,RR,\alpha)\},\\
H_{\rm rel}=\{(1,LL,0,LR,=),(1,LR,0,RL,=)\},\\
Q=\{L,R\}^3,\qquad N\ge1.
\end{gathered}
\tag{ARH.16.5}
$$

This input is in $\mathfrak S$. Its entire source fiber is exactly

$$
\left\{\langle\langle t,\rho(t)\rangle,
                  \langle\rho^2(t),\alpha\rangle\rangle:
                 t\text{ any finite branch tree}\right\}.
\tag{ARH.16.6}
$$

No deterministic source-total static or serial service has a uniform
finite new-read budget for its entire original $Q$ row.

Proof. The two equalities and two literals force (ARH.16.6), and conversely
every displayed tree gives those records with both endpoints reached.
The already supplied clock obeys $\kappa(\rho t)=\kappa(t)+1$, so
$t,\rho(t),\rho^2(t)$ are pairwise distinct. They are all branch trees,
hence each differs from the fourth old value $\alpha$. Thus all six old
inequalities hold for **every** branch $t$; none narrows the displayed
fiber further. Proposition 15.1 proves eligibility. The same paid
producer as Proposition 2.1 realizes this record schedule.

Fix $h\ge0$. Let $a$ be the complete binary tree of depth $h+1$ with
all leaves $\alpha$, and let $a'$ change exactly one depth-$h+1$ leaf
to $\beta$. They are finite, different, and agree through depth $h$.
Put $t=\langle a,a\rangle$ and $t'=\langle a,a'\rangle$.
Both are legal branch values in the entire fiber. Their original prefixes
agree through depth $h$, and (SLH.74.7) gives the same for their first
two iterates. Thus the two whole sources (ARH.16.6) agree through original
depth $h$ and preserve all retained constraints.

For both sources precisely the first six depth-three cuts are reached;
$RRL,RRR$ lie below the original $\alpha$ and are absent. The outside
context is the same, namely

$$
\langle\langle\langle\square_1,\square_2\rangle,
                       \langle\square_3,\square_4\rangle\rangle,
          \langle\langle\square_5,\square_6\rangle,\alpha\rangle\rangle.
\tag{ARH.16.7}
$$

The complete partitions differ: at $LLL,LLR$ the values are $a,a$ for
$t$ and $a,a'$ for $t'$. This differing entry witnesses inequality of
the entire required row; it does not replace the target by that bit.
As $h$ was arbitrary, these finite sources disprove every original
prefix bound. Theorem 14.1, using the inherited operational bridge,
excludes every uniform finite serial budget.

The free branch parameter ranges over all finite branch shapes, not an
orbit-index family. The target image here is nevertheless finite: the
context and reached set are fixed and only a partition of six holes
varies. Its obstruction is unbounded observation depth, not infinitely
many target rows. $\square$

## 17. The constructor-offset boundary of this representation

**Theorem 17.1 (one shifted constructor graph is not synchronous).**
The relation

$$
G=\{(x,z)\in\mathcal T^2:z=\langle x,\alpha\rangle\}
\tag{ARH.17.1}
$$

is not recognized by any finite bottom-up tree automaton on the
same-root convolution of Definition 11.1. This is a boundary of this
coordinate representation, not of the decidability of Definition 9.1.

Proof. Suppose such an automaton exists and determinize it by the finite
subset construction. For every finite tree $b$ take

$$
x_b=\langle\alpha,b\rangle,\qquad
z_b=\langle\langle\alpha,b\rangle,\alpha\rangle.
\tag{ARH.17.2}
$$

Its convolution is accepted. The right child of its root is exactly
$\operatorname{conv}(b,\alpha)$; the left child is the valid partial
convolution of $\alpha$ and $\langle\alpha,b\rangle$ with the mandated
padding. Infinitely many distinct $b$ and finitely many states give
distinct $b,c$ having the same state on $\operatorname{conv}(b,\alpha)$
and $\operatorname{conv}(c,\alpha)$.

Replace only that right child in the accepted term for $b$. The left
child and root label are unchanged, and the right state is unchanged,
so the deterministic root state remains accepting. The result is still
a valid convolution: its two whole coordinates are
$\langle\alpha,c\rangle$ and
$\langle\langle\alpha,b\rangle,\alpha\rangle$.
They violate (ARH.17.1) since $b\ne c$. This contradiction uses only
finite well-formed trees and proves the claim. $\square$

**Proposition 17.2 (the obstruction is an acquired input, not a no-service certificate).** Take $P=\{L,RL\}$, outside
$C=\langle\square_1,\langle\square_2,\alpha\rangle\rangle$, two distinct
old classes $x,y$, no literals, and the equality record $(0,L,0,R,=)$.
Its entire source fiber is

$$
\{\langle\langle y,\alpha\rangle,
          \langle y,\alpha\rangle\rangle:y\in\mathcal T\}.
\tag{ARH.17.3}
$$

The old-coordinate relation is exactly $x=\langle y,\alpha\rangle$.
For $Q=\{L,R\}$ the complete target row is constant and needs zero new
reads. This presentation is outside $\mathfrak S$ as defined above.

Proof. Both compared epoch-zero endpoints are originally reached, so
the equality is precisely $x=\langle y,\alpha\rangle$. Its old
inequality $x\ne y$ holds automatically by finite node count. These
implications reverse and give (ARH.17.3). Paid original traversal and
comparison, followed by the complete access cut, realize the retained
record. Both target holes are reached and equal, and the outside is
$\langle\square_1,\square_2\rangle$. This is a complete zero-read output.

To check failed eligibility of this actual presentation, consider the
pattern cell in which both old class patterns are complete binary
skeletons to relative frontier depth $d$. With no literal conditions
and with both endpoints reached, this cell survives the initial checks.
Its retained equality compares $t_x$ with
$\langle t_y,\alpha\rangle$. Down the left side, some depth-$d$
variable of $t_x$ faces a nonground pair in the corresponding depth-$(d-1)$
part of $t_y$. That child comparison is unsupported. The false comparison
on the right side is not a short circuit under Definition 10.1. Constraint
eligibility precedes emptiness, so this cell makes the presentation fail.
No conclusion about service impossibility follows from that failure.
$\square$

Theorem 17.1 and Theorem 8.2 concern different representation classes.
The fixed-power graph of $\rho$ is synchronous by Lemma 11.2 although it
has no finite ordinary-cell compilation in the sense of §8. Conversely,
the ordinary equation (ARH.17.1) already fails same-root convolution
recognizability. Finite constructor syntax and fixed-power synchronous
graphs therefore cannot be combined by asserting an unproved closure
under arbitrary subtree offsets. Replacing coordinates, solving a
contextual equation first, or using richer automata may cover excluded
presentations, but each such extension owes an exact source and target
correspondence and a terminating finite-prefix test. No undecidability
claim follows from either representation boundary.

## 18. Suppliers, new scope and the remaining coupled problem

The new source-relative result is the combination of a decidable
presentation family, its exact whole-row disagreement language, and the
finite descending test with a complete paid consumer. The family inclusion
and the two active non-orbit examples show an infinite class of genuinely
coupled inputs beyond the literal-history and whole-source orbit fragments.
Theorem 17.1 locates a different precise representation obstruction.
These are ordinary `repo-derived` deductions. Finite automata closure,
productive-state calculations, syntactic cancellation, the image parser
and the inherited read/service bridge are reused methods, not newly
claimed general mathematics. There is no global-priority claim.

The supplier correspondence is bounded and explicit.

- [SLH, §§59–62 and 74.2–74.4][SLH] supplies the complete old-row and
  prefix-pattern correspondence, original-coordinate locality, and the
  literal-only entire-row criterion. Proposition 3.2 supplies the
  guarded relation extension. Proposition 10.3 checks their exact
  interfaces without dropping any old or endpoint condition.
- [SLH, §69][SLH] already uses aligned suffix coordinates and finite-set
  descriptions of whole trees and their iterates for finite historical
  VALUE minimax. The shared-coordinate idea and its finite-tree semantics
  are supply. The present full-row disagreement problem includes unknown
  whole exterior trees and new complete equality partitions, so it is
  not a renamed finite VALUE task. No extension of that minimax formula
  to this task is claimed.
- [SLH, §§70–73][SLH] retains its known-ancestor and joint-extension
  results. Section 2 retains static/serial existence equivalence, and
  §§4–8 retain their root-certificate classification and ordinary-cell
  barriers. Theorem 14.1 supplies an effective family decision in addition
  to those existence and special-fiber results.
- [TATA][TATA], Theorems 1.1.9, 1.3.1 and 1.7.4, supplies determinization,
  Boolean closure and productive-state emptiness for finite ranked-tree
  automata. Here every alphabet, state set, template and formula is
  finite, and padding validity is explicitly part of the language.
  Lemma 11.2 states the concrete interpreted-graph construction;
  Theorem 13.1 proves the exact finite-prefix recurrence. Neither a
  general tree-homomorphism closure nor an emptiness theorem alone
  supplies the whole-source/full-row bridges.
- The weak-second-order finite-tree correspondence in [TATA, Lemma 3.3.4
  and Theorem 3.3.8][TATA] is alternative background for the aligned
  finite-set supplier in §69. It is not needed by the direct automata
  construction here. No quantified support is silently restricted to a
  visible finite window, and no MONA execution is asserted.
- Pinned [mathlib DFA][ST-DFA] and [NFA][ST-NFA] provide word-automaton
  closure and determinization results such as `DFA.accepts_compl`,
  `DFA.accepts_inter` and `NFA.toDFA_correct`. Their word domains are not
  the finite ranked-tree tuple domain here. They are not an exact Lean
  supplier of this coupled criterion. The bounded inspected sources
  supply no compiled application of Theorem 14.1.

For raw-price scope, the [serial-price supplier (SCR)](https://github.com/the-omega-institute/trureturing/blob/4aa70704d18ea51257d443e0c58a4d5af0da90c7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md),
Assumption 1.1 and Definition 1.2, has the exact specialization
$H=H_0$, $H_{\rm rel}=\varnothing$. Its entire domain $D$ then equals
$\mathcal U_R(H_0,\varnothing)$: the original free trees, arbitrary
original cuts, concrete old context, repeated classes and every old
cross-class disequality coincide. Its complete access cut includes every
accessible source-bearing bit. The target is the same entire original
$R_Q(u)$, and the two service classes have the same certified $N$,
arbitrary finite physical addresses, deterministic source-total behavior,
static restriction or real serial updates on one register. Actual new
raw calls are counted with repetitions; acquisition, entry, addresses,
local work, memory, certification, updates, archives and output remain
separately paid. Empty relation history introduces no comparison port.
SCR Theorems 4.2, 5.2 and 6.1 supply complete-row terminal predicates,
the two-way strategy correspondence and effective exact prices for this
literal-only domain, including zero, infinity and attaining services.
These are reused ordinary supplier results; no extension of their
minimax construction to arbitrary coupled relation constraints is made.

SCR Theorem 7.2 supplies a strict separation within that specialization.
It uses $P=\{\varepsilon\}$ with the single root-hole old row,
$H_0=((0,RL,\mathsf{absent}))$, $H_{\rm rel}=\varnothing$ and $Q=\{L\}$.
Its entire fiber is
$\{\alpha,\beta\}\cup\{\langle x,b\rangle:x\in\mathcal T,
\ b\in\{\alpha,\beta\}\}$.
The four complete outputs are the two concrete leaf rows and the two
one-hole rows $\langle\square_1,\alpha\rangle$ and
$\langle\square_1,\beta\rangle$, each with its unique one-class partition.
At the same initial $N=0$ or $N=2$, the static minimum is two new reads
and the serial minimum is one. The serial upper bound uses one real
paid update; its raw improvement does not make that update free.
The supplier's lower bounds cover every finite physical address and
all permitted deterministic services on this entire infinite fiber.
Thus universal equality of the two minima is false already for
$H_{\rm rel}=\varnothing$, hence also over the unrestricted class that
contains it. This qualifies the price wording in Definition 9.1:
literal-only exact prices are supplied, and blanket equality is refuted;
computing the two prices for arbitrary coupled histories, and thereby
deciding equality for each such input, remain outside these results.

Source comparison starts with the immutable predecessor and this volume's
existing results, then the named pinned library interfaces, then the
cited author text. This is a bounded overlap and hypothesis check, not
an exhaustive literature survey. The new decision is not attributed to
[TABG][TABG] or [OSD][OSD]: no exact reduction of all the present interpreted
constraints and prefix quantifiers to those theories is supplied. Related
full-bispectrum and late-contact results have no established source map
to this tree task and are not premises.

**Provenance and evidence boundary.** This is a single-author ordinary
mathematical synthesis under the formal-thinking-and-answer, sshx and
theory-volume-template instructions, using supplied predecessor theory,
completed advisory research conclusions, and the stated literature.
Definitions and proofs here fix one formulation; advisory alternatives
are not silently identified with it. There is no fresh Lean or kernel
proof, no retained bind-only declaration, no solver implementation or
complexity claim, and no independent approval asserted by this text.

The unchanged general question is to decide
$\exists h\,\operatorname{PrefDet}(U,Q,h)$ on **arbitrary** guarded coupled
mixed-epoch relation inputs, with arbitrary original cuts and all the
same paid/full-state conditions. Failed membership in $\mathfrak S$
leaves that question unresolved. A future extension must handle genuinely
shifted coupled terms with both directions of source correspondence,
full-row disagreement correspondence and a terminating test for arbitrarily
deep **finite admissible** counterpairs. Merely deciding satisfiability,
constructing a witness, or listing prefix candidates is insufficient.

Effective minimum raw budgets for arbitrary coupled relation histories,
joint resource optima, the original stochastic $j_c$ alternative, common
full-law calibration, exact finite stochastic optimum and effective
charged attainment remain unresolved here. The literal-only SCR prices
and the example-specific one-read minimum in Proposition 16.1 do not
supply those general conclusions. This extension advances the persistent
self-calibration programme without completing or replacing it.

[ST-DFA]: https://cdn.jsdelivr.net/gh/leanprover-community/mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Computability/DFA.lean
[ST-NFA]: https://cdn.jsdelivr.net/gh/leanprover-community/mathlib4@db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Computability/NFA.lean

## 追加锚（本行以下为增补区）
## 19. Constructor definitions with observable original coordinates

The source and service contract is Definition 1.1, Definition 1.2 and
Assumption 1.3: finite nonempty ordered trees, the interpreted substitution
$\rho$, the entire acquired fiber $U=\mathcal U_R(H_0,H_{\rm rel})$, and
the entire original row $R_Q$. The old row retains every repeated class and
every different-class disequality. Both endpoints of each relation record
must exist, including for a disequality. Literal repetitions and absent
replies retain their force. The certified initial epoch is at least every
recorded epoch. Arbitrary finite prefix-free original $P,Q$, including
empty, root and absent cuts, remain allowed.

The extension here eliminates constructor definitions while preserving
coordinates that are actual original subtrees. It gives a decidable family
of acquired inputs, an exact decision of finite original-prefix
determination on that family, and a paid whole-row consumer. Constructor
definitions may copy parameters and contain unequal fixed powers of
$\rho$. Residual constraints may couple all remaining coordinates. This
is a restricted extension of the synchronous residual method; it does not
decide arbitrary cyclic interpreted equations.

**Definition 19.1 (prefixes and normalized templates).** Write $s\equiv_h t$
when $r_s(p)=r_t(p)$ for every $|p|<h$, including absent replies. For tuples,
require this in each corresponding coordinate. Thus the inclusive depth
$h$ convention of Definition 2.2 is $\equiv_{h+1}$ here.

A normalized template over $X$ is generated by the two concrete leaves,
pairing, and decorations $\rho^a(x)$, $x\in X$, $a\in\mathbb N$.
A ground subtemplate denotes its complete finite tree. Every expression
obtained by composition, pairing and fixed powers has this form: distribute
a power over pairing, compose powers at variables, and evaluate concrete
leaf images. This is an interpreted expression, never a free unary
constructor. Normalization is a structural recursion on the finite input
expression, with finite iteration on each explicitly given exponent.
It terminates even though the resulting finite expression can be large.

**Lemma 19.2 (the algebraic interfaces used in elimination).** The following
operations and identities hold on finite trees.

1. $\rho$ is injective and has an effective partial inverse on finite trees.
2. Every normalized template preserves $\equiv_h$ in all its arguments.
3. For a fixed template $A$ and two assignments $v,w$,
   $A[v]=A[w]$ exactly when $v(x)=w(x)$ for all variables occurring in $A$.
4. A bare-variable equation $x=A$ with $x$ occurring in $A$ is false unless
   $A$ is syntactically $x$.

Proof. No $\rho$-image is $\alpha$. The only leaf image is
$\rho(\alpha)=\beta$. The tree $\langle\beta,\alpha\rangle$ has preimage
$\beta$ and cannot have a paired preimage, since the right child of the
image of a pair is itself an image and is not $\alpha$. Every other paired
image has a paired preimage exactly when both children have preimages.
Recursion on the strictly smaller children supplies the partial inverse
and proves its uniqueness. Finite iteration handles any fixed power.

For a physical address $p$ in $\rho^n(t)$, follow $p$ in the original $t$.
Until the first original leaf, every encountered pair persists. After
that leaf, the remaining reply is computed in its known finite
$\rho^n$-image. If no leaf has been encountered by $p$, its reply is branch.
Consequently the reply depends only on original replies at prefixes of
$p$, never on a deeper original reply. This includes an address born
inside an expanded leaf and an address still absent. Powers of $\rho$
therefore preserve $\equiv_h$. Pairing and ground insertion do also;
structural induction proves item 2.

For item 3 compare the same normalized template under the two assignments.
Cancel its identical pair skeleton. At every decorated occurrence the
remaining equality is $\rho^a(v(x))=\rho^a(w(x))$, equivalent to
$v(x)=w(x)$ by injectivity. Ground parts impose no condition. Repetition
only repeats a condition. The same argument works for an outside context
with fixed, distinct numbered hole symbols.

For item 4, let $\ell$ count leaves. Induction gives
$\ell(\rho(t))\ge\ell(t)$. If an occurrence of $x$ in $A$ lies below a pair,
its decorated value contributes at least $\ell(x)$ leaves and a nonempty
sibling contributes at least one more. Thus $\ell(A)>\ell(x)$. Otherwise
$A=\rho^a(x)$. For

$$
\kappa(\alpha)=0,\qquad \kappa(\beta)=1,\qquad
\kappa(\langle s,t\rangle)=2+\kappa(t),
$$

induction gives $\kappa(\rho(t))=\kappa(t)+1$. Hence $a>0$ makes equality
impossible, and $a=0$ is the identity case. These are the elementary
parser and clock interfaces already used in §§2–3 and [SLH, §§2, 55][SLH],
with the bare-variable size consequence stated explicitly. Item 4 does
not apply to $\rho^a(x)=A$: the finite solution $x=\beta$ of
$\rho(x)=\langle x,\alpha\rangle$ prevents that inference. $\square$

**Definition 19.3 (two finite original-prefix covers).** Let

$$
m=\max\bigl(\{0\}\cup\{|q|:q\in Q\}
 \cup\{|p|:(n,p,c)\in H_0\}
 \cup\{|p|,|q|:(n,p,n',q,\bowtie)\in H_{\rm rel}\}\bigr),
\qquad d=m+1.
\tag{CE.19.1}
$$

Start with $W=C[(z_{[i]})_i]$, one variable per old class, and all
$z_b\ne z_c$ for different classes. Use either of the following two fixed
finite covers. A successful cover is chosen as a whole; alternative
constructions are not combined into overlapping semantic charts.

The uniform cover is precisely the depth-$d$ old-class pattern cover of
Proposition 3.2 and [SLH, Definition 74.2][SLH]. Each repeated class uses
one shared pattern and shared frontier variables at all its occurrences.

The second cover resolves only the prescribed navigation. Process literal
requests in retained list order, then the two endpoints of each relation
in retained list order, and then original $Q$ addresses in lexicographic order.
To navigate a nonempty remaining suffix inside $\rho^n(x)$, split the
original variable $x$, simultaneously at every occurrence, into the
three disjoint cases $\alpha$, $\beta$, $\langle x_L,x_R\rangle$.
In a leaf case navigate its concrete finite $\rho^n$-image. In a pair
case distribute $\rho^n$ and consume the next address letter. A literal
request additionally resolves the root reply at its endpoint, splitting
there if needed. A relation endpoint or a reached cut endpoint can stop
at a decorated variable; its full value remains a template. For $Q$ this
navigation is at epoch zero. Recompute the affected expressions after a
shared split. Stop a branch when a literal is wrong or a relation endpoint
is absent. Otherwise stop when all requests have been resolved.

Every split is indexed by an old class and an original relative address
$s$ of length at most $m$. Once split, that variable is never split again.
No branch has more than

$$
M_0=|\mathcal B|(2^d-1)
\tag{CE.19.2}
$$

splits. Indeed a nonempty suffix can expose only an original strict
ancestor of the requested address, and a literal root test only its
endpoint; after a first original leaf there are no further original
variables on that path. Sharing can require the same split at another
occurrence, but creates no new relative address. Thus the three-way
split tree is finite, including all early rejected branches. A concrete
old context with no classes has an empty split tree.

A surviving chart $\eta$ has a pure constructor source pattern
$W_\eta(X_\eta)$; a fixed reached set $J_\eta\subseteq Q$ with its canonical
numbering; an outside context $E_\eta$; and hole terms $T_{\eta,q}$.
Every variable $x$ has a fixed reached original representative address
$a_{\eta,x}$, obtained by following its relative address inside a
representative old hole. At that occurrence the source term is literally
$x$. Attach the conjunction $\Phi_\eta$ of **all** old class disequalities
and every signed interpreted endpoint equality. Literal conditions and
endpoint existence have already been checked in the chart. No general
morphic feasibility test is used to discard a chart at this stage.

**Proposition 19.4 (exact charts and paid observable identity).** For either
cover there is a bijection

$$
\coprod_\eta\{v:X_\eta\to\mathcal T:\Phi_\eta(v)\}
 \longrightarrow U,\qquad (\eta,v)\longmapsto W_\eta[v].
\tag{CE.19.3}
$$

The chart is determined by a bounded finite original prefix. It can be
selected by at most $2M_0$ actual current reads at any certified $N$.
Within a chart, recutting and filling commute:

$$
I_Q(W_\eta[v])=J_\eta,\quad
C_Q(W_\eta[v])=E_\eta[v],\quad
(W_\eta[v])|_q=T_{\eta,q}[v].
\tag{CE.19.4}
$$

Proof. Each shared split is the exhaustive, disjoint root classification
of one finite original subtree. A paired split records its two unique
finite children. Induction on the finite decision tree gives unique
patterns and unique frontier assignments; the uniform construction is
the same argument performed to a fixed depth. Recover each variable by
its representative original subtree. By the old-row correspondence of
[SLH, Theorems 59.4 and 60.2][SLH], all old inequalities together are
exactly what makes the retained partition correct, including off-task
classes and repeated occurrences.

Induction along every endpoint navigation gives its exact value under
that assignment. Expanding a known original leaf uses its actual finite
image, so an originally absent endpoint may be reached at its recorded
epoch, while an endpoint absent at that epoch rejects either relation
sign. Repeated literal requests impose repeated, consistent conditions.
Thus $\Phi_\eta$ imposes precisely the remaining retained predicates.
Conversely every finite assignment satisfying it fills the old pattern,
preserves every old inequality and satisfies every guarded record. This
proves both directions of (CE.19.3), not just satisfiability preservation.
Original absent $P$ addresses remain blocked by the old concrete context.

The finite selector asks only original constructor questions at fixed
representative addresses. Different charts first differ at one such
question. Each can be recovered from the current register by [SLH,
Theorem 2.2][SLH] in at most two actual reads, including absent relative
replies. In the uniform cover, asking all relative $|s|<d$ questions per
old class gives the same bound. The maximum address length in this finite
selector is an effective original-prefix bound. These observations prove
selection without an uncharged semantic test.

No $Q$ navigation continues into an unresolved variable. Replacing that
variable by any nonempty tree cannot change a reached endpoint, its
numbering, or an absent endpoint already blocked by an original leaf.
Recutting therefore commutes with filling, which proves (CE.19.4).
For empty $Q$ the entire $W_\eta[v]$ is exterior; for $Q=\{\varepsilon\}$
the exterior is one numbered hole and its partition is one class.
These cases are included. $\square$

## 20. A finite constructor-elimination recognizer

**Definition 20.1 (sound comparison reduction and factoring).** Normalize
terms as in Definition 19.1. To reduce an equality, delete syntactic
identities, evaluate fully ground comparisons, cancel two pairing heads,
and reject different concrete constructor heads. A ground tree facing a
pair is opened at its root for this cancellation. A decorated variable
facing a ground tree is tested by the partial inverse of Lemma 19.2.
The result is false or a bare-variable equality with the unique inverse.
Two decorations may cancel a common power. For a bare variable occurring
in the other side use precisely item 4 of that lemma. All these rules
preserve truth under every finite assignment.

Apply these equality rules inside a disequality by negating the **entire**
reduced equality formula. In particular
$\langle A,B\rangle\ne\langle D,E\rangle$ becomes
$\neg(A=D\land B=E)$, not the conjunction of two disequalities.
Use ordinary Boolean constant simplification. A residual equality not
covered by a rule is retained as an unsupported atom, not declared false.

For a normalized term $T$, define a partial operation $L_a(T)$:

- For ground $g$, return its unique $a$-fold inverse if it exists.
- For $\rho^b(y)$ with $b\ge a$, return $\rho^{b-a}(y)$.
- For a non-ground pair, recursively factor both children and pair the
  results if both succeed.
- Otherwise report failure.

Ground processing has priority over the pair rule. Structural induction,
using the actual leaf parser, proves

$$
L_a(T)=V\quad\Longrightarrow\quad
T[v]=\rho^a(V[v])\quad\hbox{for every finite assignment }v.
\tag{CE.20.1}
$$

This operation terminates by descent through $T$, together with finite
partial inversions on ground pieces. Failure has no semantic implication.
For example a non-ground pair can specialize to $\rho(\beta)$ without
admitting a uniform childwise inverse. No leaf-image solution is removed.

**Definition 20.2 (permitted elimination and eligibility).** Only an
atomic equality known as a mandatory positive conjunct of $\Phi_\eta$
may be used as a definition. Pair cancellation exposes both children of
a mandatory positive equality as mandatory conjuncts. An atom under a
disjunction or negation is not selected, and a task-hole equality is not
assumed to hold.

For either orientation $\rho^a(x)=T$, if $L_a(T)=V$ succeeds and $x$ does
not occur in $V$, substitute $V$ for $x$ in every remaining constraint,
the source pattern, the outside context and every hole term. Remove the
now-true defining equation, normalize, and reduce comparisons again.
Bare $x=T$ is included with $a=0$. Do not introduce new variables in this
phase. Record the completely composed substitution

$$
\sigma:X_\eta\longrightarrow\operatorname{Templates}(Y_\eta),
\qquad Y_\eta\subseteq X_\eta,\qquad \sigma(y)=y\ (y\in Y_\eta).
\tag{CE.20.2}
$$

A formula is *synchronous residual* when reduction leaves a Boolean
combination of constants and atoms

$$
\rho^a(y)=\rho^b(z),\qquad \rho^a(y)=g,
\tag{CE.20.3}
$$

with $g$ a complete finite ground tree. These denote actual tree relations.
For a chart search all permitted elimination schedules, including stopping
immediately and stopping after any step. It is eligible if one schedule
either yields a constant contradiction in its domain, or makes both its
remaining domain $D_\eta=\Phi_\eta[\sigma]$ and every reached-hole equality

$$
e_{\eta,qr}(v):=
[T_{\eta,q}[\sigma][v]=T_{\eta,r}[\sigma][v]],\qquad q<r\in J_\eta,
\tag{CE.20.4}
$$

synchronous residual. A chart with a synchronous domain that is empty
may also be discarded, using the finite automaton test of Lemma 21.1,
without requiring its target comparisons to reduce.

An input belongs to $\mathcal E_{\rm CE}$ if at least one of the two
covers of Definition 19.3 has every surviving chart eligible. Choose one
such cover and one witnessing schedule per chart, all from common input.
There is no new branch choice depending on unknown parameter equality.
An input failing this recognizer is **outside this theorem**. That result
is never a certificate of service nonexistence.

**Proposition 20.3 (termination and exact elimination).** Membership in
$\mathcal E_{\rm CE}$ is decidable. On an accepted input, write

$$
F_\eta=W_\eta[\sigma],\qquad
\bar E_\eta=E_\eta[\sigma],\qquad
\bar T_{\eta,q}=T_{\eta,q}[\sigma].
$$

Then $v\mapsto F_\eta[v]$ is a bijection from the finite assignments
satisfying $D_\eta$ to the entire original fiber in that chart. At every
surviving representative $a_{\eta,y}$ its original subtree is exactly
$v(y)$. No extra original sources are lost or gained by the presentation.

Proof. Comparison reduction terminates by recursive descent through two
pairing heads, finite ground evaluation, or a terminal identity, atom,
clash or bare occurs case. Common-power cancellation is done once on a
pair of decorations, and factoring is a terminating test. A local rule
is not repeatedly reoriented. Ground inversion and Boolean simplification
are finite. Between eliminations no rewrite feeds a larger term back into
an unrestricted root-splitting procedure.

Every elimination removes one active variable. At a fixed stage there
are only finitely many mandatory equalities and two orientations of each;
each factoring test has at most one result. Hence the search tree has
finite branching and depth at most $|X_\eta|$, even if terms grow.
The two covers and all their charts are finite. The residual syntax test
is decidable; its optional emptiness check is the finite construction of
Lemma 21.1. This proves recognition termination without assuming a
complete interpreted unification algorithm.

By (CE.20.1) and injectivity, the selected equation is exactly $x=V$.
Since $x$ does not occur in $V$, restriction to the other coordinates is a
bijection from its conjunction with the remaining constraints to those
constraints after substitution. The inverse assigns the unique finite
value $V[v]$ to $x$. Substitution commutes with interpreted evaluation
by induction on terms and formulas. It therefore preserves all signed
constraints jointly, even when a variable repeats or occurs in many old
inequalities. Induction on the number of eliminations gives (CE.20.2)
and the asserted finite-assignment bijection. A contradiction discards
only a genuinely empty chart.

Combine this with (CE.19.3). Each remaining $y$ was originally a leaf
variable of the source pattern at $a_{\eta,y}$. No other variable can be
an ancestor of that occurrence in the pattern. Substituting for other
variables leaves that occurrence literally $y$. Consequently restriction
back to those original subtrees is the inverse map. Reconstructed values
of eliminated coordinates are finite templates of finite trees, so they
cannot be rational or infinite-tree solutions. $\square$

**Proposition 20.4 (the two original-prefix directions).** In each accepted
chart,

$$
\begin{aligned}
v\equiv_h w&\Longrightarrow F_\eta[v]\equiv_h F_\eta[w],\\
F_\eta[v]\equiv_{A_\eta+h}F_\eta[w]
 &\Longrightarrow v\equiv_h w,
\qquad A_\eta=\max(\{0\}\cup\{|a_{\eta,y}|:y\in Y_\eta\}).
\end{aligned}
\tag{CE.20.5}
$$

Proof. The first line is Lemma 19.2 applied to the reconstructed source
template, including all introduced offsets and copied occurrences.
For the second, inspect each original representative followed by every
suffix of length less than $h$, using Proposition 20.3. Empty parameter
tuples satisfy both statements. The finite selector of Proposition 19.4
additionally separates distinct charts. Thus later tests within charts
omit no arbitrarily close cross-chart pair. $\square$

## 21. The checked synchronous interface for complete-row disagreement

This section records only the finite automaton interface needed by the
constructor presentation. Its graph construction and productive-prefix
method are reused synchronous methods. Automaticity is asserted in the
surviving-coordinate presentation, not in the old tuple with constructor
offsets still present.

**Lemma 21.1 (finite residual automata).** Boolean combinations of
(CE.20.3) have effectively constructible finite bottom-up automata on
padded convolutions of their finite tree coordinates. Emptiness is
decidable and a nonempty relation supplies a finite witness. The same
holds after adjoining a finite list of coordinate-prefix conditions.

Proof. The convolution has the union of the coordinate domains. A label
lists their symbols in $\{\alpha,\beta,\mathsf{pair},\bot\}$, excluding
the all-padding tuple; its arity is two if a coordinate is a pair and
zero otherwise. Validity requires each root coordinate present; at a
binary node a paired coordinate has two present children, while a leaf
or padded coordinate has padded children. These are finite local checks.

After cancelling common powers, a variable-variable atom is a graph
$x=\rho^k(y)$ in one orientation. A finite grammar for that graph has
one recursive production with pair/pair root and two graph children,
and two complete ground productions

$$
\rho^k(\alpha)\otimes\alpha,
\qquad \rho^k(\beta)\otimes\beta.
\tag{CE.21.1}
$$

Induction on finite $y$ proves exactness in both directions. Expand the
finite ground productions into finitely many ordinary automaton states.
Ground atoms use the unique partial inverse, or are false, and ground
equality has a finite automaton. Coincident variable names in an atom
are handled by using the same coordinate twice, including possible
self-power conditions; no independence is assumed.

To lift an atomic automaton to a larger tuple, inspect its selected
coordinates. Where all selected coordinates are padded, use a blank
state. Where selected coordinates have already terminated but other
coordinates continue, simulate their nullary transition and require
selected blank states below. Otherwise simulate the selected transition.
This deals explicitly with projection changing the union-domain arity.
Intersect with tuple validity. Products, union and powerset
complementation relative to valid tuples implement every Boolean formula.
Coordinate-prefix restrictions use finite inspections of labels and
padding and have finite automata too. Finally compute productive states
from nullary transitions by repeated binary closure. Recording a first
production for each new state constructs finite witnesses; intersection
with final states decides emptiness. All steps terminate on finite state
sets. These are the usual finite-tree automata constructions, specialized
to the exact interpreted graphs (CE.21.1). $\square$

**Definition 21.2 (the entire-row bad-pair relation).** Let $O_\eta$ be the
set of surviving parameters occurring in $\bar E_\eta$, including decorated
occurrences. On two copies of the surviving tuple define

$$
\begin{aligned}
\operatorname{Bad}_\eta(v,w):={}&D_\eta(v)\land D_\eta(w)\land\\
&\left(\bigvee_{y\in O_\eta}v(y)\ne w(y)
 \ \lor\!\bigvee_{q<r\in J_\eta}
       \bigl(e_{\eta,qr}(v)\mathbin{\mathsf{xor}}e_{\eta,qr}(w)\bigr)\right).
\end{aligned}
\tag{CE.21.2}
$$

Empty disjunctions mean false. Every condition in $D_\eta$ is retained in
both copies. In particular this is not a product of marginal feasibility
conditions. Lemma 21.1 constructs an automaton $\mathcal A_\eta$ for this
relation. A zero-parameter chart has at most one source and empty Bad.

**Proposition 21.3 (whole-row fidelity).** For finite assignments satisfying
the domain, $\operatorname{Bad}_\eta(v,w)$ holds if and only if
$R_Q(F_\eta[v])\ne R_Q(F_\eta[w])$.

Proof. Equation (CE.19.4) remains true after exact substitution. The
reached original addresses, order and numbered holes are fixed in the
chart. Equality of its two concrete exteriors is exactly equality of
all parameters visible in $\bar E_\eta$, by item 3 of Lemma 19.2.
Parameters under removed holes impose no exterior requirement. The two
complete partitions agree exactly when every unordered pair of reached
holes has the same equality status; (CE.20.4) computes each status exactly.
Negating these two necessary and sufficient agreements gives (CE.21.2).
This covers the entire concrete exterior even when it can be very large.
A common parameter canceled from a hole equality is not made relevant
again merely because it occurs in the compared terms. $\square$

**Lemma 21.4 (productive finite-prefix test).** Let $S_\eta,F^{\rm acc}_\eta$
be the state and final-state sets of $\mathcal A_\eta$. A convolution label
is diagonal when each corresponding $v,w$ symbol agrees, including
padding. Put $Z_0$ equal to the productive states and set

$$
Z_{j+1}=\{s:\text{a diagonal nullary transition yields }s\}
 \cup\{s:\text{a diagonal binary transition from }s_L,s_R\in Z_j
                         \text{ yields }s\}.
\tag{CE.21.3}
$$

The sequence decreases and stabilizes effectively. Its stable set is
$Z_\infty$. There is a finite $h$ with no admissible bad pair
$v\equiv_h w$ exactly when

$$
F^{\rm acc}_\eta\cap Z_\infty=\varnothing.
\tag{CE.21.4}
$$

If (CE.21.4) fails, for each given $h$ one can construct a finite
admissible bad pair satisfying $v\equiv_h w$.

Proof. Induct on $j$: $s\in Z_j$ exactly when a finite convolution-shaped
input has a run to $s$ and all its labels at depths less than $j$ are
diagonal. At zero this is productivity. At the next level a diagonal
nullary root terminates, or a diagonal binary root joins two finite
witnesses from the preceding level. This proves both directions of the
induction. Intermediate witnesses need not have valid coordinate roots;
validity is enforced at acceptance by $\mathcal A_\eta$.

In particular $Z_1\subseteq Z_0$. Monotonicity of the displayed operation
then gives $Z_{j+1}\subseteq Z_j$. There are at most $|S_\eta|$ strict
decreases; after equality, further iterations are equal. On a valid
accepted convolution, diagonal labels through $j$ levels are exactly
$v\equiv_j w$. Addresses outside the union domain are absent in both
copies and cause no missing comparison. Hence a final state in $Z_j$
is precisely a finite bad pair with that prefix agreement.

If the stable intersection is empty, the finite stabilization computation
finds such a $j$. If it is nonempty, for any requested $j$ retain transition
witnesses for its $j$ recurrences and attach productive finite completions
at level $j$. This is a finite construction even for a state participating
in cycles. Acceptance supplies valid finite trees and the full Bad
predicate. No infinite tree, arbitrary unproductive state or compactness
limit substitutes for these witnesses. $\square$

## 22. Exact determination and a paid original-row consumer

**Theorem 22.1 (constructor-elimination full-row criterion).** For every
nonempty acquired input in $\mathcal E_{\rm CE}$, the following are
equivalent:

1. Every nonempty selected chart satisfies (CE.21.4).
2. Some finite original prefix determines the entire $R_Q$ on the entire
   $U=\mathcal U_R(H_0,H_{\rm rel})$.
3. For every permitted certified $N$, a deterministic effective static
   service returns that entire row, is total on $U$, and has a uniform
   finite bound on its new raw calls.
4. Such a service exists at a permitted $N$ when real paid serial
   $\mathsf{ApplyRho}$ is allowed.

The criterion is effective. A negative answer constructs, for every
requested inclusive original depth $b$, two finite sources in $U$ with
identical replies at $|p|\le b$ and different entire $Q$-rows. The theorem
does not equate general minimum static and serial prices.

Proof. Construct the chosen finite cover, its elimination schedules and
its residual automata. Emptiness removes exactly the empty domains.
For each remaining chart satisfying (CE.21.4), find $h_\eta$ with
$F^{\rm acc}_\eta\cap Z_{h_\eta}=\varnothing$. Let $s$ be a prefix length
that contains all questions in the original chart selector, and take

$$
H=\max\bigl(\{s\}\cup\{A_\eta+h_\eta:\eta\text{ nonempty}\}\bigr).
\tag{CE.22.1}
$$

Two sources in $U$ agreeing under $\equiv_H$ choose the same chart.
By (CE.20.5) their remaining coordinate tuples agree under
$\equiv_{h_\eta}$. Lemma 21.4 excludes Bad, and Proposition 21.3 gives
equality of the entire rows. This proves 1 implies 2. There is no
unobserved normalization branch whose selection is being assumed.

Conversely, if a chart fails, use Lemma 21.4 at $h=b+1$. Its two finite
assignments satisfy the complete joint domain and Bad. Proposition 20.3
reconstructs two finite sources in the same original chart of $U$;
(CE.20.5) gives their original agreement at all $|p|\le b$ and Proposition
21.3 gives their different full rows. This disproves 2 and proves the
claimed effective finite negative witnesses.

For the operational implication, let $M$ be the maximum number of
original literal questions in the chosen finite selector, so $M\le M_0$.
At static epoch $N$ recover those replies with [SLH, Theorem 2.2][SLH],
using at most $2M$ actual reads. This selects the actual chart, necessarily
nonempty. For each surviving $y$, the original node $a_{\eta,y}$ is known
to exist and its current subtree is $\rho^N(v(y))$. Recover every original
relative reply with $|p|<h_\eta$ there using the same decoder, prefixing
every actual query by $a_{\eta,y}$. Its absence guard applies to relative
addresses as well. A sufficient uniform new raw bound is

$$
K=2M+\max_{\eta\text{ nonempty}}
           2|Y_\eta|(2^{h_\eta}-1).
\tag{CE.22.2}
$$

Only genuine $N$-epoch addresses and replies are raw events. Decoded
original facts are logical consequences of those events, not fabricated
historical acquisitions. The register remains at $N$ throughout.

Intersect the domain automaton for $D_\eta$ with these finite coordinate
prefix conditions and extract any accepted finite assignment $w$.
The actual assignment proves nonemptiness. Thus this finite local
computation terminates. Compute the entire finite
$R_Q(F_\eta[w])$ and output it. The actual assignment and $w$ have equal
observed prefixes, so Lemma 21.4 and Proposition 21.3 prove that their
entire rows coincide. There is no assertion that $F_\eta[w]$ is the actual
source. Its row is an evaluator of a value proved common to the whole
conditioned domain. Extra decoder replies need not be matched by $w$:
the proof already gives the same row on the larger domain selected by
the decoded facts alone. They remain actual retained evidence if retained.
This gives 1 implies 3, and 3 implies 4 by inclusion of service classes.

For 4 implies 2 reuse the operational argument of §2 and [SLH, Theorem
74.4, proof (iii)][SLH] at its exact interface. A source-total deterministic
service with at most $K$ four-valued reads has finitely many reachable
reply prefixes. Between successive reads, its deterministic computation,
real updates and eventual next address or output are fixed by such a
prefix and must terminate on every source reaching it. Therefore the
submitted physical addresses on all reachable prefixes form a finite set.
Let $B$ exceed all their lengths. Original $\equiv_B$ agreement forces the
same reply at each submitted address at its actual, possibly adaptive,
epoch, by Lemma 19.2's address locality. Induction gives the same complete
serial transcript and output. Correctness forces equal entire rows.
This argument assumes no extra source information from update timing,
identity, hidden control or retained caches, exactly as Assumption 1.3
requires. It does not assume a prior uniform work or update bound.
Thus 4 implies 2 and all four statements are equivalent. $\square$

**Proposition 22.2 (resources, acquisition and boundary cases).** Theorem
22.1 preserves the actual acquisition/full-access-cut contract and all
separately charged resource coordinates. Empty cuts, absent original
endpoints and zero-parameter charts introduce no extra operation.

Proof. If $Q$ is empty, Bad compares the entire exterior, which is the
entire original tree. If $Q$ is the root cut, Bad is empty. An absent
original $Q$ address is omitted only after its finite original guard has
been resolved; a later birth does not create an original hole. If there
are no old classes, the old context already fixes the source; all checks
are ground. If elimination leaves no parameters, a consistent chart has
one reconstructed finite source. The same proofs cover each case.

The raw bound (CE.22.2) depends only on common retained input and the chosen
finite calculation, not on the unknown source or on the allowed $N$.
$N$ changes physical decoder addresses. The prefix phase has maximum
address length at most

$$
\max\bigl(\{|p|:p\text{ a selector question}\}
 \cup\{|a_{\eta,y}|+h_\eta-1:h_\eta>0,\ y\in Y_\eta\}\cup\{0\}\bigr)
 +\lceil N/2\rceil.
\tag{CE.22.3}
$$

Actual address construction and transmission, local computation, finite
images and substitutions, automata determinization, witness construction,
working memory, installation, entry, certification, versions, updates,
archives and full output are separately charged. They may be large.
No practical complexity or joint-resource optimum follows from finiteness.

The formal constraints do not certify that any record was acquired.
Assumption 1.3 remains necessary. Proposition 2.1 supplies a compatible
producer: paid traversal of the original source computes its complete
old row; paid traversals acquire each existing endpoint at its stipulated
epoch; every requested literal, including repeats and absence, is actually
read; real updates take place on the same register; comparisons use only
those already paid finite descriptions. An absent relation endpoint gives
a distinct invalid outcome. The producer is finite on each finite source.
Under the stipulated complete cut it retains exactly the declared records,
certified epoch and common control, making every other source-bearing
value, count, timing field, handle and archive inaccessible. Its successful
output fiber is exactly the conjunction used here, in both directions.
This is a conditional mathematical access correspondence, not a physical
erasure guarantee or a uniform acquisition-price claim. No consumer can
recover forgotten trees for free from a retained comparison sign.

The resulting output row does not automatically define a new complete
access cut: all newly acquired replies and remaining old information
must be accounted for by any subsequent forgetting contract. $\square$

## 23. Family inclusion and coupled constructor-offset examples

**Proposition 23.1 (a broad sufficient family and the synchronous inclusion).**
The family $\mathcal E_{\rm CE}$ includes every input passing the supplied
synchronous residual test on the uniform cover. More generally, in either
cover suppose the mandatory equalities contain finitely many definitions

$$
\rho^{a_i}(x_i)=T_i,\qquad L_{a_i}(T_i)=V_i,
\tag{CE.23.1}
$$

whose selected-variable dependency graph $x_i\to x_j$ for occurrences of
$x_j$ in $V_i$ is acyclic. Suppose substituting these definitions in
dependency order makes every remaining domain and target comparison
synchronous residual, or proves the domain empty. If every chart has
this property, the input belongs to $\mathcal E_{\rm CE}$.

This admits arbitrary finite constructor templates and copying, for
example

$$
x=\langle\rho(y),\rho^2(z)\rangle,
\qquad
\rho^2(w)=\langle\rho^3(y),\rho^4(z)\rangle,
\tag{CE.23.2}
$$

followed by any jointly retained Boolean combination of supported
residual comparisons. The second equation reconstructs
$w=\langle\rho(y),\rho^2(z)\rangle$. The remaining domain is not required
to be a product, and residual fixed-power cycles are allowed.

Proof. The empty elimination schedule on the unchanged uniform cover
witnesses the first inclusion; our reduction includes its constructor,
ground and common-power rules. For the second claim, process definitions
whose selected dependencies have already been eliminated. Acyclicity
ensures that the right side of the resulting definition contains no
occurrence of its selected variable. Every such step is permitted by
Definition 20.2 and has the exact interpretation (CE.20.1). The resulting
successful finite schedule appears in the exhaustive finite search.
All charts, including infeasible charts not yet proved empty, are subject
to the stated requirement. This is a syntactic sufficient inclusion,
not a claim that every acyclic interpreted system can be normalized.
The next examples prove that the first inclusion is strict at the
specified synchronous-frontier interface. $\square$

**Proposition 23.2 (an acquired coupled six-hole entire fiber).** Let

$$
P=\{LL,LR,R\},\qquad
C=\langle\langle\square_1,\square_2\rangle,\square_3\rangle,
\qquad \pi=\{\{1\},\{2\},\{3\}\}.
\tag{CE.23.3}
$$

Retain literals $(0,RLR,\alpha)$ and $(0,RRR,\beta)$ and positive records

$$
(1,LL,0,RLL,=),\qquad(2,LR,0,RRL,=).
\tag{CE.23.4}
$$

Also retain the three signed records

$$
(0,LL,2,LR,\ne),\qquad
(0,LR,1,LL,\ne),\qquad
(1,LL,2,LR,\ne).
\tag{CE.23.5}
$$

For any certified $N\ge2$, the entire original fiber is exactly

$$
\begin{aligned}
u(x,y)&=\langle\langle x,y\rangle,
       \langle\langle\rho(x),\alpha\rangle,
                    \langle\rho^2(y),\beta\rangle\rangle\rangle,\\
D(x,y)&:\quad x\ne y\ \land\ x\ne\rho^2(y)
        \ \land\ y\ne\rho(x)\ \land\rho(x)\ne\rho^2(y),
\qquad x,y\in\mathcal T.
\end{aligned}
\tag{CE.23.6}
$$

Take the unchanged original cut

$$
Q=\{LL,LR,RLL,RLR,RRL,RRR\}.
\tag{CE.23.7}
$$

This acquired input belongs to $\mathcal E_{\rm CE}$. It fails the
unmodified synchronous test on its uniform old-class frontier cover.
Its entire row has a static consumer using at most two new actual reads.

Proof. Write the three old class values as $x,y,z$. The two literal
leaves force
$z=\langle\langle a,\alpha\rangle,\langle b,\beta\rangle\rangle$.
Original-address transport in (CE.23.4) forces $a=\rho(x)$ and
$b=\rho^2(y)$. The three negative records are precisely the final three
conditions in $D$; their endpoints exist because $LL,LR$ are original
holes. The old $x\ne y$ is still required. The remaining two old
inequalities are automatic, since

$$
\ell(z)=\ell(\rho(x))+\ell(\rho^2(y))+2
          >\ell(x),\ell(y).
\tag{CE.23.8}
$$

Thus necessity gives (CE.23.6), and every finite $(x,y)$ satisfying $D$
gives exactly all the retained data, including the complete three-class
old partition. Both directions use the entire joint domain. Neither
parameter has a size or shape bound.

For all-chart eligibility use the navigation cover, with the literal
requests first. To reach $RLR$ and $RRR$ it splits $z$, its left child
and its right child. Every wrong ancestor-leaf case is rejected; the
terminal literals fix the two displayed leaf values. No request needs
the root label of $x,y,a,b$. Thus there is exactly one surviving chart
before its joint constraints are imposed:

$$
W=\langle\langle x,y\rangle,
           \langle\langle a,\alpha\rangle,\langle b,\beta\rangle\rangle\rangle.
\tag{CE.23.9}
$$

Eliminate $a=\rho(x)$ and $b=\rho^2(y)$. The two old inequalities involving
$z$ reduce by the bare-variable occurs rule (or (CE.23.8)); the old
$x\ne y$ remains. The domain is exactly the synchronous conjunction
$D$. The six complete hole values, in order, are

$$
x,\ y,\ \rho(x),\ \alpha,\ \rho^2(y),\ \beta.
\tag{CE.23.10}
$$

Every comparison of these is between decorated variables or a decorated
variable and a ground leaf. Hence all target comparisons pass too.
Rejected navigation branches were rejected only by actual literals.
This verifies eligibility for every chart, not just a selected source.

For strictness, the uniform cover uses $d=4$. Let $B_j$ be the perfect
height-$j$ tree with all leaves $\alpha$. Choose
$x=B_{d+2}$ and $y=B_{d+4}$. They satisfy $D$: their clocks are $2d+4$
and $2d+8$, and the four clocks of $x,y,\rho(x),\rho^2(y)$ are distinct.
Consider their nonempty uniform chart. At original $RLL$ a full value
$\rho(x)$ is nested two levels inside the old $z$ class. At its suffix
$LL$, a $z$-frontier variable $c$ is compared with the known pairing
$\rho(x|_{LL})$, whose non-ground descendants still contain $x$-frontier
variables. Pair cancellation therefore leaves $c=T$ with $T$ a
non-ground pairing of decorated $x$ variables. The supplied synchronous
test stops at just this unsupported shape. The chart contains the finite
source just displayed, so infeasibility cannot remove it. The same
misalignment persists at any common deeper old-class frontier with
sufficiently tall $x,y$. Elimination changes coordinates; it does not
assert that the old constructor-offset graph was synchronous.

All six holes are reached and their entire outside context is

$$
\langle\langle\square_1,\square_2\rangle,
       \langle\langle\square_3,\square_4\rangle,
                    \langle\square_5,\square_6\rangle\rangle\rangle.
\tag{CE.23.11}
$$

The four values at holes $1,2,3,5$ are pairwise different: use $D$ and
$\kappa(\rho^j(t))=\kappa(t)+j$. No positive image is $\alpha$, and no
second image is $\beta$, by the partial inverse. Besides singleton
identities, the complete partition is consequently generated by

$$
\begin{array}{c|c}
\text{condition}&\text{hole equality}\ \hline
x=\alpha&1=4,\quad 3=6\\
x=\beta&1=6\\
y=\alpha&2=4\\
y=\beta&2=6.
\end{array}
\tag{CE.23.12}
$$

These exhaust all fifteen unordered comparisons; any transitive
consequence is taken when canonicalizing the partition. Incompatible
root combinations simply cannot occur under $D$.

Use the known-existing-subtree root decoder [SLH, Definition 2.1][SLH]
at actual addresses

$$
LLR^{\lceil N/2\rceil},\qquad LRR^{\lceil N/2\rceil}.
\tag{CE.23.13}
$$

Here concatenation follows $LL$ or $LR$ by the displayed power of $R$.
At positive even $N$, replies $\alpha,\beta,\mathsf{branch}$ give the
three original root cases directly. At odd $N$, replies
$\mathsf{absent},\alpha,\{\beta,\mathsf{branch}\}$ give respectively
$\alpha,\beta,\mathsf{branch}$. Output (CE.23.11), all six original hole
addresses and the complete partition (CE.23.12). These are two paid
queries on the actual register and the whole original row is returned.
The bound holds on every finite $(x,y)$ in $D$, independently of $N$.

The consumer is active: set $y=\langle\alpha,\alpha\rangle$. Both
$x=\alpha$ and $x=\beta$ satisfy $D$ (the potentially compared transformed
values are branches with the indicated distinct clocks), and their
partitions in (CE.23.12) differ. Hence zero calls cannot suffice, even
with real updates. No claim of an exact two-call minimum is needed.

For actual acquisition use Proposition 2.1 with this fixed schedule:
paid original acquisition supplies the old row and all epoch-zero
endpoints; the two specified literals are actually issued; one real
update and paid $LL$ traversal supply its epoch-one value; a second real
update and paid $LR$ traversal supply its epoch-two value. Compare only
paid descriptions to obtain (CE.23.4)–(CE.23.5). After any additional real
updates to the certified $N$, impose the complete cut. The producer's
matching output has exactly (CE.23.6) as its fiber. $\square$

**Proposition 23.3 (the same target with finite negative witnesses).** Delete
only (CE.23.5), keeping $P,R,H_0$, (CE.23.4), $Q$ and $N$ as above.
The entire fiber becomes

$$
U^- =\{u(x,y):x,y\in\mathcal T,\ x\ne y\}.
\tag{CE.23.14}
$$

It still belongs to $\mathcal E_{\rm CE}$, but no permitted source-total
serial or static service has a uniform finite new-read budget.

Proof. The same two-direction derivation and (CE.23.8) leave exactly the
old $x\ne y$. The same single navigation chart and two eliminations work;
the domain and all comparisons of (CE.23.10) remain synchronous. This is
an all-chart negative instance of Theorem 22.1.

Explicitly fix an inclusive depth $b$. Let $x=B_{b+3}$ and $y=\rho(x)$.
In $y$, change the leaf at address $L^{b+3}$ from $\beta$ to $\alpha$,
obtaining $y'$. These are different finite trees with equal replies at
all relative depths at most $b$. This leaf lies outside the right spine,
so $\kappa(y')=\kappa(y)=\kappa(x)+1$. Consequently $x\ne y$ and
$x\ne y'$, preserving the full old partition in both reconstructed
sources. The changed third class is recomputed according to its retained
definitions, rather than held as an independently chosen value.

Lemma 19.2 gives $u(x,y)\equiv_{b+1}u(x,y')$. Both are finite members of
the entire fiber (CE.23.14). All six original holes exist. Holes $2,3$
are equal in the first and unequal in the second. Thus their entire
rows differ. This exhibits finite bad pairs at every requested depth;
the finite-reply-tree implication in Theorem 22.1 excludes every uniform
finite raw budget, including all allowed adaptive serial updates.
The source domain and the complete six-hole target have not been reduced
to that one witnessing comparison. $\square$

## 24. Canceled parameters and boundaries of the presentation

**Proposition 24.1 (a common unbounded parameter can be irrelevant).** Let
$g=B_3$, the perfect height-three all-$\alpha$ tree. Set

$$
P=\{LL,RL,RR\},\qquad
C=\langle\langle\square_x,g\rangle,
              \langle\square_x,\square_y\rangle\rangle,
\qquad H_0=H_{\rm rel}=\varnothing,
\tag{CE.24.1}
$$

with old classes $\{LL,RL\}$ and $\{RR\}$ distinct. Its entire fiber is
$u(x,y)=\langle\langle x,g\rangle,\langle x,y\rangle\rangle$ with
$x\ne y$. For $Q=\{L,R\}$ the complete original row is determined by
the sole condition $y=g$: its outside is $\langle\square_1,\square_2\rangle$
and the two holes are equal exactly under that condition. The input is
in $\mathcal E_{\rm CE}$ and the criterion answers positively, although
$x$ remains unbounded and appears in both compared trees.

Proof. This is the exact old-row correspondence with a repeated class.
Free constructor cancellation gives

$$
\langle x,g\rangle=\langle x,y\rangle
                 \quad\Longleftrightarrow\quad y=g.
\tag{CE.24.2}
$$

In the uniform depth-two cover, every old inequality reduces to ordinary
synchronous equalities under negation: both patterns have the same
frontier depth, and a shorter concrete leaf produces a ground test or
constructor clash. Each target equality cancels the common $x$ pattern
and compares the $y$ pattern with ground $g$, again yielding only ground
tests. Thus every chart is eligible with no elimination. The outside
has no surviving variable. In its Bad formula $x$ can affect feasibility
via $x\ne y$ but has no independent output-disagreement term.

Agreement through the four relative levels $|p|<4$ of $y$ decides whether
$y=g$: the eight matching depth-three leaf replies force the entire
finite tree, including its shape, by complete-leaf rigidity. Therefore
Bad has no pair with that coordinate-prefix agreement, and Lemma 21.4
answers positively. Alternatively, eight actual delayed-leaf probes
below the originally reached $RR$ node, as in [SLH, Theorem 55.3][SLH],
test $y=g$ at any certified $N$ and output the stated entire row.
All costs other than these eight raw calls remain separate.

The equality and inequality rows both occur while $x$ remains large:
choose $x=B_4$ and take $y=g$ or $g$ with one deepest leaf changed to
$\beta$. Thus requiring every parameter occurring in the two compared
terms to become ground would be false. Only actual exterior dependence
and the exact reduced equality status belong in (CE.21.2). This example
checks fidelity to the already supplied literal-history result
[SLH, Definitions 74.3–74.4][SLH]; it is not a new literal-price theorem.
$\square$

**Proposition 24.2 (what exact representation alone does not supply).**
A finite source presentation with a synchronous domain and constant
whole row in each chart does not by itself imply finite original-prefix
determination. Bounded original-prefix chart selection, or an explicit
decision of cross-chart Bad, is also necessary for the cellwise argument.

Proof. For the old one-hole root row and no history, use charts
$\alpha$, $\beta$, $\langle x,x\rangle$, and
$\langle x,y\rangle$ with $x\ne y$. These are an exact finite disjoint
presentation of all finite sources; their domains are synchronous and
$Q=\{L,R\}$ has a constant entire row on each chart. Every within-chart
Bad is empty. But finite $t,t'$ can agree arbitrarily deeply while being
different. The sources $\langle t,t\rangle$ and $\langle t,t'\rangle$
then have arbitrarily deep identical original prefixes and different
full two-hole partitions. Equality-chart identity has no bounded-prefix
selector. Definitions 19.3 and 20.2 avoid this error: all branch selection
is an original constructor question, and elimination introduces no
semantic branches. $\square$

**Definition 24.3 (the remaining interpreted constraint obligation).**
The recognizer supplies neither a complete normalizer for arbitrary
$\rho^a(x)=T$ nor a decision for an unsupported chart. In particular
failure of $L_a$, inability to eliminate a cyclic definition, or a
remaining decorated-variable/non-ground-constructor target comparison
is an eligibility failure only. The finite solution
$(x,y,z)=(\beta,\beta,\alpha)$ of
$\rho(x)=\langle y,z\rangle$ forbids a branch-only inverse rule that
would replace $x$ by a pair. The solution $x=\beta$ of
$\rho(x)=\langle x,\alpha\rangle$ likewise forbids an unqualified
interpreted occurs check.

The synchronous methods here do not make constructor-offset graphs
synchronous in the original coordinates. For the particular graph
$y=\langle x,\alpha\rangle$, the supplied convolution obstruction can
be checked directly. Suppose a deterministic bottom-up automaton
recognized it. In the accepted convolution for
$x=\langle\alpha,t\rangle$ and
$y=\langle\langle\alpha,t\rangle,\alpha\rangle$, the $LR$ cone is the
one-sided padding of $t$ and the other occurrence of $t$ lies in the
disjoint $R$ cone. Two different finite $t,t'$ give the same state on
that one-sided cone. Replacing only the $LR$ cone preserves acceptance
and valid convolution, but makes $y=\langle\langle\alpha,t'\rangle,\alpha\rangle$
while $x$ stays fixed. This contradicts the graph. Determinization covers
nondeterministic recognizers. This is a representation obstruction, not
an undecidability theorem. Theorem 22.1 uses an exact change to recoverable
original coordinates instead.

Finite productivity must also remain part of the decision. Infinite
pair trees can satisfy $\rho(\Omega)=\Omega$, whereas every finite $t$
satisfies $t\ne\rho(t)$ by its clock. Passing to arbitrary infinite
solutions can therefore change complete partitions. Neither infinite
solutions, satisfiability alone, a finite output image, nor a sampled
source family settles the finite original-prefix question.

## 25. Supplier correspondence, new content and open targets

The source-relative addition is the exact, terminating constructor-
definition presentation with surviving original-subtree coordinates,
its two prefix directions and bounded chart selector, and its application
to the entire exterior/reached-hole/partition target and paid consumer.
Propositions 23.2–23.3 exhibit acquired, non-product, constructor-offset
fibers beyond the unchanged uniform synchronous frontier test. This is
`repo-derived` ordinary mathematics. No global originality, priority,
solver implementation, Lean compilation or kernel-validation claim is
made. Standard substitution and finite automata are reused methods.

The supplier correspondences are deliberately restricted:

- [SLH, Theorem 69.4][SLH] supplies its finite historical VALUE minimax;
  [SLH, §§70–73][SLH] supply their known-ancestor merging and joint
  constraints. They are neither replaced nor redescribed as this
  constructor extension. [SLH, Theorem 74.4][SLH] supplies the entire
  arbitrary-recut literal-history criterion, the finite patterns and
  operational finite-prefix argument used at the stated interfaces.
- The published §§1–3 supply actually acquired signed histories, both
  endpoint guards, complete old-row fibers and the general static/serial
  existence bridge. The root-descendant orbit fragment and the ordinary
  free-term cell compilation barrier retain their separate scopes.
  Neither is needed as a new theorem here.
- The fixed-power convolution construction, Boolean closure and
  productive diagonal-prefix test are the synchronous supplier interface.
  Lemmas 21.1 and 21.4 check exactly that interface for surviving finite
  original coordinates. They supply no closure of constructor-offset
  graphs on the old tuple. No statement from an unexamined continuation
  is a premise of the constructor/prefix proof.
- The separate ordinary literal-history complete-row price source
  [SCR][CE-SCR] has domain $\mathcal U_R(H)$ without arbitrary relation
  records. Its exact static/serial prices are not transferred to
  $\mathcal U_R(H_0,H_{\rm rel})$. The bound (CE.22.2) is a constructive
  upper bound, not a new general minimum-price formula.
- At repository commit
  `e7cb431501d5ebd423603bea476ebefcce3090af`,
  [`ActualTreeReadoutAcquisition.source_foundation`][CE-ACQ] includes
  complete-leaf rigidity on finite sources. Its original Boolean policy
  and fixed-source execution are not the present serial entire-row
  contract. [`adaptive_leaf_count_le_pow`][CE-COUNT] has an explicit
  finite branch count and depth. The operational use here instantiates
  four reply alternatives after source-total deterministic segments are
  compressed; it does not import a hidden uniform work bound.
- The pinned mathlib [`Term.realize_subst` and
  `BoundedFormula.realize_subst`][CE-SEM] state that substitution commutes
  with realization. Interpret the language's pairing and unary operation
  on $\mathcal T$ by the actual pairing and $\rho$. These statements match
  the semantic substitution step in Proposition 20.3; they do not supply
  eligibility completeness, tree-automaton construction or a paid source
  consumer. This correspondence is not a compiled application.
- [Lin, *Accelerating tree-automatic relations*, §3 and Proposition 1][CE-LIN]
  uses the union-domain padded convolution and gives effective logical
  closure for a **given** tree-automatic presentation. The finite ranked
  alphabet and graph grammars in Lemma 21.1 furnish that presentation.
  No acceleration theorem or complexity bound from that paper is used.
  This is `literature-attested` automata background, not an external
  theorem about this acquired source fiber.

The bounded supplier inspection is of those pinned declarations,
published theory interfaces, and the primary convolution/closure result.
It establishes no repository-wide or literature-wide absence theorem.
The ordinary proofs provide the new source/application bridge themselves;
no unverified solver, binding-only retained declaration or formal approval
is supplied. The exposition uses the formal-thinking, SSHX and
[theory-volume-template][CE-TEMPLATE] conventions as an independent
ordinary author fragment; it is not independent review of itself.

The unrestricted problem remains the effective decision, for arbitrary
finite actually acquired guarded coupled $H_{\rm rel}$, whether a single
finite original prefix determines the entire $R_Q$ on the entire nonempty
finite-source fiber. Residual cyclic decorated-constructor constraints
and unsupported target comparisons still require a richer exact
representation or another complete bounded-disagreement method. Any such
method must preserve all old inequalities, both finite-source directions,
original-prefix observation and finite negative witnesses; failure of
this recognizer gives no negative answer to that problem.

General minimum raw budgets for arbitrary $H_{\rm rel}$, joint-resource
optima and charged attainment remain open. The original stochastic
$j_c$ alternatives, joint full-law calibration, finite exact stochastic
optimum and effective charged stochastic attainment are unchanged.
This deterministic constructor extension advances the persistent
self-calibration programme and does not complete or replace it.

[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[CE-SCR]: https://github.com/the-omega-institute/trureturing/pull/15374
[CE-ACQ]: https://github.com/the-omega-institute/trureturing/blob/e7cb431501d5ebd423603bea476ebefcce3090af/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[CE-COUNT]: https://github.com/the-omega-institute/trureturing/blob/e7cb431501d5ebd423603bea476ebefcce3090af/D5/S3/Observer/Budget/WorstCaseDepthInformationLowerBound.lean
[CE-SEM]: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/ModelTheory/Semantics.lean
[CE-LIN]: https://anthonywlin.github.io/papers/fsttcs12.pdf
[CE-TEMPLATE]: ../../../skills/theory-volume-template/SKILL.md

## 追加锚（本行以下为增补区）
## 26. Reuse-only application: rigid feedback and exact literal histories

This section is a reuse-only application of the classification and orbit
calculations in Theorems 4.2, 5.2 and 6.1, with the source, row and service
correspondences of §§1–2. Items
26.1–26.9 spell out the parameter substitutions and resulting calculations;
they are not new mathematical declarations or a new mathematical
increment. In particular, feedback rigidity is an instance of Theorem
4.2, and exchanging the two root branches gives the already classified
atomic orbit. The whole-row consumer does not change that reuse status.

The application concerns one fixed acquired feedback equation. The source
domain, literal replies, original rows and paid service contract are those
of Definitions 1.1–1.2 and Assumption 1.3. Write $\mathsf{Pair}$ for the
reply denoted $\mathsf{branch}$ there. Every tree below is finite. Fix

$$
\begin{gathered}
P=\{L,RL,RR\},\qquad
C=\langle\square_1,\langle\square_2,\square_3\rangle\rangle,
\qquad \pi=\{\{1,2\},\{3\}\},\\
H_{\rm rel}=\bigl((1,L,0,R,=)\bigr).
\end{gathered}
\tag{CS.26.1}
$$

The old row is exactly the presentation
$u=\langle x,\langle x,z\rangle\rangle$ with $x\ne z$.
Allow any finite list $H_0$ of certified literal records, preserving every
occurrence, and any finite prefix-free original cut $Q$. No additional
relation records are included. For service claims the complete retained
fiber is nonempty, and the actual certified epoch $r$ is at least one and
at least every epoch in $H_0$. Empty fibers will also be detected by the
mathematical calculation.

Put

$$
T_0=\alpha,\qquad T_1=\beta,\qquad
T_{j+2}=\langle T_{j+1},T_j\rangle,\qquad
u_j=\langle T_{j+1},\langle T_{j+1},T_j\rangle\rangle
    =\langle T_{j+1},T_{j+2}\rangle.
\tag{CS.26.2}
$$

The existing classification and guarded orbit formulas give the exact fiber

$$
\mathcal U_R(H_0,H_{\rm rel})
   =\{u_j:j\in S(H_0)\},
\tag{CS.26.3}
$$

where $S(H_0)$ is effectively an empty set, a finite integer interval, or
an integer tail $[A,\infty)\cap\mathbb N$. We compute the entire original
$Q$-row at every index. On an infinite retained tail a finite original
prefix determines that row exactly when $Q$ covers every infinite binary
branch. Finite retained intervals admit effective exhaustive separation.

**Application 26.1 (Theorem 4.2: finite feedback rigidity).** On all finite trees,

$$
\rho(x)=\langle x,z\rangle
\quad\Longleftrightarrow\quad
\exists j\ge0\ (x,z)=(T_{j+1},T_j).
\tag{CS.26.4}
$$

The index is unique, and every displayed solution has $x\ne z$.

Parameter substitution. If $\rho(x)=\langle x,z\rangle$, then $L$ is
reached in $\rho(x)$ and $x=(\rho(x))|_L$. Apply Theorem 4.2 to the
finite tree $x$ with $(n,m,p)=(0,1,L)$. It gives $x=T_k$ for $k\ge1$.
Equation (ARH.4.2) gives
$\rho(x)=T_{k+1}=\langle T_k,T_{k-1}\rangle$; ordered-pair cancellation
therefore gives $z=T_{k-1}$. Set $j=k-1$. Conversely (ARH.4.2) supplies
the displayed equation for every $j\ge0$. The index injectivity already
supplied in Definition 4.1 gives uniqueness and $x\ne z$.

Both endpoints in (CS.26.1) are reached for every source with that old row:
the first is $\rho(x)$ and the second is $\langle x,z\rangle$.
Consequently this application gives the two directions of (CS.26.3) before
literal intersection. In the converse direction all three original old
holes are reached, the first two values coincide, and the third differs;
thus the *complete* old partition is exactly $\pi$. Also

$$
\rho^a(u_j)=u_{j+a}\qquad(a,j\ge0).
\tag{CS.26.5}
$$

For the remaining reuse, let $\sigma$ exchange just the two root branches
of a pair, and let $\sigma(\varepsilon)=\varepsilon$,
$\sigma(Ls)=Rs$, $\sigma(Rs)=Ls$ on addresses. Then
$u_j=\sigma(T_{j+3})$ and
$\rho^a u_j=\sigma(T_{j+a+3})$. Nonroot reached subtrees and literal
replies correspond at the exchanged addresses; both root replies are
$\mathsf{Pair}$. A cut $Q$ corresponds to $\sigma(Q)$. To recover its
entire original row, exchange the root branches of the concrete exterior,
relabel every reached hole in the lexicographic order for $Q$, and carry
the complete partition along that same bijection. For the root cut use
the single-hole row. Empty cuts retain the entire exchanged tree.
This is a mathematical coordinate correspondence, not a physical
root-exchange operation. It preserves completeness of a cut, all literal
occurrences and their epochs, and the whole exterior. The orbit-index,
row and service calculations in the proofs of Theorems 5.2 and 6.1 apply
under this correspondence and the exact fiber from Application 26.1.
This reuse adds no acquired root-certificate record: the sole retained
relation remains literally (CS.26.1).

Neither $\rho$ nor its feedback equation is treated as a free constructor
or subjected to a free-term occurs check.

**Application 26.2 ((ARH.4.3): guarded addresses and replies).** Let
$w(L)=1$, $w(R)=2$, and let $w$ add along a word, with $w(\varepsilon)=0$.
For a nonempty address $p=\ell s$, $\ell\in\{L,R\}$, define

$$
\begin{aligned}
h(Ls)&=1+w(s),& h(Rs)&=w(s),\\
g(\ell s)&=\begin{cases}
0,&s=\varepsilon,\\
h(\ell s)-w(b),&s=t b\ne\varepsilon,
\end{cases}
\end{aligned}
\tag{CS.26.6}
$$

where $b$ is the last letter of $s$. Then $0\le g(p)\le h(p)$, and

$$
\begin{aligned}
p\in\operatorname{Pos}(\rho^a u_j)
 &\Longleftrightarrow j+a\ge g(p),\\
(\rho^a u_j)|_p&=T_{j+a+2-h(p)}
                 \quad\text{when reached}.
\end{aligned}
\tag{CS.26.7}
$$

At the root the subtree is $u_{j+a}$, always reached with reply
$\mathsf{Pair}$.

Parameter substitution. Equation (ARH.4.3) already supplies, for nonempty
$s$ with parent word $s^-$,

$$
s\in\operatorname{Pos}(T_n)
 \Longleftrightarrow n\ge w(s^-)+2,
\qquad T_n|_s=T_{n-w(s)}\quad\text{when reached}.
\tag{CS.26.8}
$$

Apply it to $T_{j+a+1}$ on the left and $T_{j+a+2}$ on the right.
For $s\ne\varepsilon$ the guards become respectively
$j+a\ge1+w(s^-)$ and $j+a\ge w(s^-)$, precisely (CS.26.6).
For $p=L,R$ both child roots always exist. Subtracting $w(s)$ gives
(CS.26.7) in all reached cases; no nonnegative-index convention replaces
the supplied reach guard.

In particular, a nonnegative proposed subtree index is not by itself a
reach test. For example $p=LL,j=a=0$ proposes index zero but is absent:
$g(LL)=1$. The guard must be checked first.

**Application 26.3 (Theorem 5.2: exact literal-history intersection).** For a
literal record $e=(a,p,c)$ let $I_e$ be the set of indices giving its
stated reply at its own certified epoch. At $p=\varepsilon$, $I_e$ is
$\mathbb N$ for $c=\mathsf{Pair}$ and is empty otherwise. At a nonempty
$p$, put $h=h(p)$ and $g=g(p)$. The exact sets are

$$
\begin{array}{c|l}
c&I_{(a,p,c)}\\ \hline
\mathsf{absent}&\{j\in\mathbb N:j\le g-a-1\}\\
\alpha&\{h-a-2\}\cap\{j\in\mathbb N:j+a\ge g\}\\
\beta&\{h-a-1\}\cap\{j\in\mathbb N:j+a\ge g\}\\
\mathsf{Pair}&\{j\in\mathbb N:j\ge\max(0,h-a)\}.
\end{array}
\tag{CS.26.9}
$$

Define, as an intersection over the retained list with all occurrences,

$$
S(H_0)=\mathbb N\cap\bigcap_{e\text{ an occurrence in }H_0}I_e.
\tag{CS.26.10}
$$

This proves (CS.26.3) exactly, including emptiness. Every $I_e$ is an
integer interval or empty. Their finite intersection has exactly one of
the three forms stated above; in particular it has no separated finite
part preceding a disconnected tail.

Proof. Absence is exactly failure of (CS.26.7). Under that guard the
subtree index $n=j+a+2-h$ is nonnegative. Its root is $\alpha$ exactly
when $n=0$, is $\beta$ exactly when $n=1$, and is a pair exactly when
$n\ge2$. These facts give the two guarded singleton lines. For the last
line $n\ge2$ is $j+a\ge h$, which implies the guard because $h\ge g$.
These cases exhaust the replies, including endpoints born after epoch zero.

For computation, start with lower bound zero and upper bound $+\infty$.
An empty $I_e$ makes the result empty; otherwise intersect its lower and
upper bounds with the running bounds. A finite singleton supplies both
bounds. At the end lower bound above upper bound means empty, a finite
upper bound gives a finite interval $[A,B]\cap\mathbb N$, and infinite
upper bound gives $[A,\infty)\cap\mathbb N$. Maxima of lower bounds and
minima of upper bounds prove this exhaustive classification.

Every original source satisfying the retained input first has the form
$u_j$ by Application 26.1 and then satisfies every set membership in
(CS.26.10). Conversely a $j$ in that intersection produces a finite $u_j$
with the complete old row, the guarded acquired equality, and every
literal at its stated epoch. This proves both full-source inclusions;
there is no additional promise that the source belongs to the family.
$\square$

Identical records may have identical effects on the intersection, but
remain distinct acquired occurrences. Different epochs are never merged.
For example $(0,LL,\mathsf{absent})$ and $(1,LL,\beta)$ both hold exactly
at $j=0$; recording both, or repeating either, is legitimate. Treating
the absent reply as an absence at every epoch would give a false result.

For clarity about signs, the relation convention remains literally

$$
\operatorname{Rel}_{(a,p,b,q,\bowtie)}(u_j)
\Longleftrightarrow
G_{a,p}(j)\land G_{b,q}(j)\land
\bigl(V_{a,p}(j)\bowtie V_{b,q}(j)\bigr),
\tag{CS.26.11}
$$

where $G_{a,\varepsilon}$ is true, $G_{a,p}(j)$ for nonempty $p$ means
$j+a\ge g(p)$, and $V$ is the entire subtree in (CS.26.7), or $u_{j+a}$
at the root, defined only under its guard. For a disequality it is the
last comparison alone that is negated; both guards stay conjoined.
Here the sole retained relation is (CS.26.1), whose two guards were
verified above. The old $x\ne z$ compares reached old holes and holds
by index distinctness. Formula (CS.26.11) fixes the semantic convention;
this application does not add arbitrary signed records to its input class.

**Application 26.4 (Definition 1.1 and Theorem 5.2: the entire row).**
Given $j\ge0$ and finite prefix-free $Q$, the following finite calculation
returns the entire row, including all concrete exterior trees.

If $Q=\{\varepsilon\}$, its reached list is $(\varepsilon)$, its exterior
is $\square_1$, and its partition is $\{\{1\}\}$. Otherwise its reached
list is the lexicographic ordering of

$$
J_j=\{q\in Q:j\ge g(q)\}.
\tag{CS.26.12}
$$

Number this list $q_1,\ldots,q_m$. Starting at the root of the finite
$u_j$, perform first-hit cutting: at $q_i$ return $\square_i$ without
descending; at any other reached leaf return its concrete label; at any
other reached pair return the ordered pair of the two recursive results.
Denote the resulting concrete context by $E_j^Q$. The full partition is

$$
i\sim_j k\quad\Longleftrightarrow\quad h(q_i)=h(q_k).
\tag{CS.26.13}
$$

Thus the actual row is the tuple $(J_j,E_j^Q,\pi_j)$, with the reached
list made explicit in addition to the usual context/partition notation.
For $Q=\varnothing$ this is
$(\varnothing,u_j,\varnothing)$.

Calculation. The recursion is exactly Definition 1.1's whole-context
cutting on the known finite $u_j$; it leaves no unknown exterior variable.
Equation (CS.26.7) at epoch zero gives the reached list and the whole
value $T_{j+2-h(q_i)}$ at each reached nonroot hole. The supplied index
injectivity in Definition 4.1 gives (CS.26.13), as in Theorem 5.2's
whole-row calculation. A root cut is the sole cut by prefix freeness;
an empty cut removes no node.

**Application 26.5 (Theorems 5.2–6.1: the entire-exterior condition).** On the
family $(u_j)_{j\ge0}$, or on any infinite retained tail of it, the entire
exterior $E_j^Q$ is eventually constant if and only if $Q$ covers every
infinite binary branch. Equivalently,

$$
\sum_{q\in Q}2^{-|q|}=1.
\tag{CS.26.14}
$$

If this holds and $Q\ne\{\varepsilon\}$, define

$$
B_Q=\max\bigl(\{0\}\cup\{g(q):q\in Q\}\bigr).
\tag{CS.26.15}
$$

For every $j\ge B_Q$ the *actual fixed row* is

$$
\left(Q,\operatorname{Trie}(Q),\pi_Q\right),\qquad
q\sim_{\pi_Q}q'\Longleftrightarrow h(q)=h(q').
\tag{CS.26.16}
$$

Here $Q$ is ordered lexicographically and $\operatorname{Trie}(Q)$ is the
finite full binary trie with a pair at every proper prefix and its
numbered holes at the cut addresses. It contains no $j$, no $T_j$ and no
unfilled source variable. For the root cut set $B_Q=0$ and use its fixed
one-hole row from Application 26.4.

Calculation. This is Definition 5.1's completeness test and the constant
trie case in Theorems 5.2–6.1, using the guards $g(q)$ and equality keys
$h(q)$ from Application 26.4. Equivalently, at depth
$M=\max(\{0\}\cup\{|q|:q\in Q\})$, the disjoint extensions of the cut
words cover exactly $\sum_{q\in Q}2^{M-|q|}$ of the $2^M$ words. This
gives (CS.26.14), including empty and root cuts. Above $B_Q$ all cuts
are reached, so the complete-trie calculation gives (CS.26.16).

For the converse it is useful to make all surviving exterior cones
explicit. If $Q$ is nonempty and has no root cut, let $M_Q$ consist of
the missing children of its trie: addresses $p a$ where $p$ is a proper
prefix of a member of $Q$, $a\in\{L,R\}$, and $p a$ is a prefix of no
member of $Q$. Set $M_\varnothing=\{\varepsilon\}$ and
$M_{\{\varepsilon\}}=\varnothing$. Then

$$
F_Q=Q\cup M_Q
\tag{CS.26.17}
$$

is a finite complete prefix-free frontier. Every member of $M_Q$ is
incomparable with every member of $Q$. Indeed a branch in the finite trie
either first hits a cut leaf or first takes a missing child; these are
exactly its first hits in $F_Q$. This proves all the assertions, including
that $M_Q$ is nonempty exactly when $Q$ is incomplete.

For a sufficiently large explicit threshold, take
$B_{F_Q}=\max(\{0\}\cup\{g(p):p\in F_Q,\ p\ne\varepsilon\})$.
At every $j\ge B_{F_Q}$ the full exterior can equivalently be computed by
the finite trie of $F_Q$: put the numbered $Q$ holes at $Q$ and put at each
$m\in M_Q$ the *complete finite tree*

$$
\begin{cases}
u_j,&m=\varepsilon,\\
T_{j+2-h(m)},&m\ne\varepsilon.
\end{cases}
\tag{CS.26.18}
$$

Expand these finite trees when forming the actual row. Every exterior
node is included by this construction. No $Q$ cut enters or removes an
$M_Q$ cone, and all its ancestors are pairs. If $m\ne\varepsilon$, its
surviving subtree changes at every distinct index by distinctness of
the $T_n$. If $m=\varepsilon$, then $Q$ is empty and the whole $u_j$
changes; its left subtree already distinguishes its index. Thus an
incomplete $Q$ has different concrete exteriors at any two distinct
indices beyond this threshold, including on every retained tail.
It cannot have an eventually fixed row. $\square$

Formula (CS.26.18) is an evaluation rule for a changing exterior, not a
claim that a symbolic family is one row. In the complete case (CS.26.16)
is literally a single finite tuple after its threshold. For finite
retained $S$, eventual behavior along an infinite tail is not invoked.

**Application 26.6 (Theorem 6.1: finite same-fiber bad pairs).**
Suppose $S(H_0)=[A,\infty)\cap\mathbb N$ and $Q$ is incomplete. Then

$$
\begin{gathered}
\forall D\in\mathbb N\ \exists u,v\in\mathcal U_R(H_0,H_{\rm rel}),
\quad u\ne v,\\
\bigl[\forall p\in\{L,R\}^*,\ |p|\le D
       \Longrightarrow r_u(p)=r_v(p)\bigr],
\qquad R_Q(u)\ne R_Q(v).
\end{gathered}
\tag{CS.26.19}
$$

Both sources can be constructed effectively as finite trees from $D$
and the common retained data.

Proof. Construct $M_Q,F_Q,B_{F_Q}$ as above and choose

$$
j=\max(A,B_{F_Q},2D+2),\qquad k=j+1,\qquad
u=u_j,\quad v=u_k.
\tag{CS.26.20}
$$

Both indices lie in the exact intersection (CS.26.10), so all old
conditions and every acquired record hold in each source. Their left
subtrees are distinct, so the sources are distinct. At a nonempty address
$p$ of length at most $D$ we have $h(p)\le2D$; (CS.26.9) at epoch zero
therefore makes both replies $\mathsf{Pair}$. The root reply is also a
pair. For $D=0$ only this root assertion is needed. Hence they agree on
the complete original $D$-prefix, including all addresses in its domain.

Take any $m\in M_Q$. Equation (CS.26.18) gives different surviving whole
subtrees there in the two exteriors, with the empty-cut case included.
Thus their entire rows differ, irrespective of any equality of their
hole partitions. All constructed trees are finite; the witnesses depend
on $D$ and impose no size bound on the full source fiber. $\square$

The quantifiers in (CS.26.19) refute one uniform finite original-prefix
bound for this retained family. By the inherited implication (ARH.2.3)
they also exclude a uniform finite new-read budget for a source-total
service under Assumption 1.3, including permitted real serial updates.
They do not state that all source-total procedures fail to terminate.
A terminating procedure with an unbounded source-dependent read count
is given below.

**Application 26.7 ((ARH.4.3): original-prefix correspondence).** For
every $j,r\ge0$ and every nonempty original address $p=a s$, define

$$
\iota_r(a s)=a L^r s.
\tag{CS.26.21}
$$

Then

$$
\begin{aligned}
r_{\rho^r u_j}(\iota_r(p))&=r_{u_j}(p),\\
\iota_r(p)\in\operatorname{Pos}(\rho^r u_j)
 &\Longleftrightarrow p\in\operatorname{Pos}(u_j),\\
(\rho^r u_j)|_{\iota_r(p)}&=u_j|_p
                \quad\text{when reached}.
\end{aligned}
\tag{CS.26.22}
$$

The original root reply is already known to be $\mathsf{Pair}$.

Proof. At side $a=L$ put $b=1$, and at side $a=R$ put $b=2$.
The current subtree there is $T_{j+r+b}$. If $r>0$, (CS.26.8) permits
$r$ left steps because $j+r+b\ge r+1$, and yields exactly $T_{j+b}$.
For $r=0$ this is immediate. Thus the current subtree at $aL^r$ is
exactly the original subtree at $a$. Navigating any suffix $s$ in those
equal finite trees gives all three statements, including absence below
their leaves. $\square$

Consequently a complete original prefix through inclusive depth $D$ can
be recovered at the actual static epoch $r$ by at most
$2^{D+1}-2$ paid reads, one at $\iota_r(p)$ for each nonempty $|p|\le D$.
Their lengths are $r+|p|\le r+D$. This is a correspondence proved on the
entire exact acquired fiber, rather than a reset to an old physical
version. The raw evidence consists only of those actual epoch-$r$
replies.

**Application 26.8 (Theorem 6.1 and (ARH.2.3): complete-row consumers).**
For the nonempty retained input (CS.26.1), arbitrary finite $H_0$, and
arbitrary finite prefix-free original $Q$, the following are equivalent:

1. A finite original prefix determines the entire $R_Q$ on the exact
   retained finite-source fiber.
2. At every permitted certified $r$, a deterministic source-total static
   consumer has a uniform finite new-read bound for that entire row.
3. Such a consumer exists at a permitted epoch with real paid serial
   updates allowed.
4. $S(H_0)$ is finite, or $Q$ covers every infinite binary branch.

All parts of this restricted decision are effective. The positive
consumers return the concrete exterior, reached original holes, and the
complete partition; the negative answer supplies (CS.26.19).

Proof. The history intersection and completeness test are finite integer
and trie calculations. To separate known candidate indices, for $t\ge0$
make one literal read at the physical address $L^{r+t+1}$. On every
source $u_k$ in the entire family its exact reply is

$$
r_{\rho^r u_k}(L^{r+t+1})=
\begin{cases}
\mathsf{absent},&k<t,\\
\beta,&k=t,\\
\mathsf{Pair},&k>t.
\end{cases}
\tag{CS.26.23}
$$

To verify this, use (CS.26.21) on the original address $L^{t+1}$.
For $t>0$ its guard is $k\ge t$ and its reached subtree is
$T_{k+1-t}$. For $t=0$ its subtree is always $T_{k+1}$, and the same
reply table holds. Thus $\beta$ tests exactly $k=t$ on this whole fiber.

If $S$ is finite, generate every finite $u_j$ for $j\in S$ and compute
its entire row by Application 26.4. Testing all but the last index in a
fixed order, accepting exactly a $\beta$ reply, either identifies a
matching candidate or leaves only the last. This gives exhaustive
separation of the finite sources and returns their exact rows. A
sufficient raw bound is $|S|-1$, zero for a singleton. Finiteness imposes
no arbitrary cutoff: the finite set is exactly the history intersection.
It also gives a finite original-prefix bound directly. For each pair of
distinct finite candidates compute a differing original address and take
the maximum of their finitely many lengths (zero for a singleton).
Agreement at that depth identifies the candidate. Equivalently the
original tests $L^{t+1}$ in (CS.26.23) give such a finite bound.

If $S=[A,\infty)\cap\mathbb N$ and $Q$ is complete, compute $B_Q$ and
the actual fixed tuple (CS.26.16), including its root-cut convention.
The exceptional set

$$
E=S\cap\{0,\ldots,B_Q-1\}
\tag{CS.26.24}
$$

is finite. Compute its individual whole rows by Application 26.4 and test
each $t\in E$ by (CS.26.23). A match selects that candidate's row. If
all tests reject, the exact interval description implies the actual
index is at least $B_Q$, so return the fixed tuple (CS.26.16).
This service is total with at most $|E|$ new reads; if $E$ is empty it
uses none. Original addresses $L^{t+1}$ for $t\in E$ also show directly
that one finite original prefix selects a row: equality of those
replies either selects the same exceptional source or puts both sources
in the constant-row tail. The root cut always needs zero reads.

These constructions prove 4 implies 1 and 2. Statement 2 implies 3 by
inclusion of service classes, and 3 implies 1 by (ARH.2.3), with exactly
the complete-state and source-totality hypotheses of Assumption 1.3.
If 4 fails, Application 26.6 refutes 1 at every requested depth.
This proves the equivalence. $\square$

For any nonempty $S$ and any $Q$, even in the negative boundedness case,
one may test $t=0,1,2,\ldots$ in (CS.26.23) until $\beta$ occurs. On
$u_k$ this takes exactly $k+1$ reads, terminates, and identifies the
original finite tree; Application 26.4 then computes its row. Thus the
negative conclusion is a failure of a *uniform* finite budget and a
uniform finite prefix, not a universal nontermination theorem.

**Application 26.9 (a one-read consumer of two complete rows).** Let
$H_0=\varnothing$ and $Q=\{LL,LR,RL,RR\}$. The entire retained fiber is
$\{u_j:j\ge0\}$. Its complete original rows are exactly

$$
\begin{array}{c|c|c|c}
j&\text{reached cuts}&\text{entire exterior}&\text{complete partition}\\
\hline
0&(RL,RR)&\langle\beta,\langle\square_1,\square_2\rangle\rangle
 &\{\{1\},\{2\}\}\\
\ge1&(LL,LR,RL,RR)&
\langle\langle\square_1,\square_2\rangle,
        \langle\square_3,\square_4\rangle\rangle
 &\{\{1,4\},\{2\},\{3\}\}.
\end{array}
\tag{CS.26.25}
$$

At every certified permitted epoch $r$, one paid read at $L^{r+1}$
returns $\beta$ exactly when $j=0$ and $\mathsf{Pair}$ exactly when
$j\ge1$, selecting these entire rows.

Proof. The empty intersection leaves all $j\ge0$. At $j=0$ the original
left child is $T_1=\beta$, so $LL,LR$ are absent, while $RL,RR$ contain
$\beta,\alpha$. This gives the first row, including its concrete exterior
leaf. At $j\ge1$ all four cuts are reached, and their whole values in
lexicographic order are

$$
T_j,\quad T_{j-1},\quad T_{j+1},\quad T_j.
$$

Index distinctness gives exactly the second partition. All exterior
nodes are the three displayed pairs. The read is (CS.26.23) with $t=0$;
its whole reached subtree is $T_{j+1}$. Both rows occur at the same
retained input, so zero reads cannot distinguish them under deterministic
common control, even with unobserved real updates. Thus one is also the
minimum new-read count for this particular example. $\square$

**Acquisition and resource correspondence.** Proposition 2.1 supplies a
compatible actual producer for this fixed schedule. Paid traversal at
epoch zero computes the entire old row and acquires the complete subtree
at $R$. After one real update, paid traversal at $L$ acquires its entire
current subtree; finite comparison of the two paid descriptions supplies
the sign in (CS.26.1). Every literal occurrence is actually read at its
own epoch, including repeated requests and absent replies. The earlier
description is kept until comparison is possible, and further stipulated
updates reach the certified service epoch. No access to an old physical
register is needed to compare already acquired descriptions.

Under the complete access cut of Assumption 1.3 the accessible state is
exactly the stated records, certified epoch and common parameters and
control. Every finite source producing this retained state satisfies its
old row and all records; conversely every finite source in (CS.26.3)
produces that same successful retained state under the fixed schedule
and cut. The original $R$ and the entire original source stay fixed
throughout. Acquisition traversal lengths, source descriptions and any
other source-bearing fields cannot remain as undeclared information.
The complete cut is the same conditional access assumption as before,
not a conclusion of the algebraic equation.

All consumers operate on the same register at its certified epoch.
A test (CS.26.23) has physical address length $r+t+1$; the example has
length $r+1$. Requests and any repetitions are paid. Address formation
and transmission, pre-cut acquisition, finite comparison, local tree
construction and row computation, installation, entry, working memory,
retention, epoch/version evidence, real updates, archives and complete
output remain separate resource coordinates. Bounds above concern new
raw calls only; no joint-resource optimum or general price formula is
asserted. A finite pre-cut cost for each source need not have a uniform
bound. There is no reset, reroot, clone, identity port, free subtree
comparison, or observable source-dependent update timing. A later entry
after an absorbing halt remains separately supplied and paid. Producing
a row does not erase accessible old data or new replies; any subsequent
cut owes its own complete-state correspondence.

**Scope and reuse status.** This is ordinary application exposition of
the existing `repo-derived` results, not an additional mathematical
increment. Theorem 4.2 supplies the feedback classification; (ARH.4.2)–
(ARH.4.3) supply transport, index injectivity and guarded addresses;
Theorems 5.2 and 6.1 supply the orbit/history and complete-row machinery.
The explicit root-exchange correspondence, finite interval intersection
and prefix embedding only specialize those results. Definitions 1.1–1.2,
Assumption 1.3, Proposition 2.1 and (ARH.2.3) retain their full source,
acquisition and service conditions. No new lemma, invariant, complexity
bound or non-bind-only theorem is asserted here. No general cyclic
normalizer or automaton closure under constructor offsets is used.

Arbitrary additional $H_{\rm rel}$, arbitrary guarded coupled cyclic
interpreted equations, and unsupported target comparisons in the earlier
recognizers remain outside this result. In particular the unrestricted
decision of Definition 9.1 and §25 remains open. The present negative
quantifiers concern the specified retained tail and specified whole-row
task only. They prove neither general impossibility nor undecidability.
General mixed-history minimum prices, joint resource optima and the
stochastic targets listed in §25 are unchanged. No new formal or kernel
result, implementation, independent approval or publication is claimed.

## 追加锚（本行以下为增补区）

## 27. The entire acquired graph with arbitrary retained literals and cuts

The result in §§27–31 is a total decision for the graph input (ARH.8.5),
with every finite mixed literal history retained and with an arbitrary
finite prefix-free original target cut. There is no target-eligibility
test. Its additional ingredient is a classification of comparisons
between holes whose underlying positions in the graph parameter are
nested. Comparisons at incomparable positions use the existing
synchronous finite-prefix decision. These two uses are joined on the
entire original source fiber, including the concrete exterior.

The symbols and graph input of §§27–32 are local to those sections.
Section 26 concerns the different old cut $P=\{L,RL,RR\}$ and record
$(1,L,0,R,=)$ of (CS.26.1), whose fiber is its exchanged atomic orbit.
Here the old cut is $P=\{L,R\}$ and the record is $(0,L,1,R,=)$:
the parameter $y$ ranges over every finite tree consistent with $H_0$.
Neither section's source promise is substituted for the other's.

**Definition 27.1 (graph input and prefix convention).** Keep
$P=\{L,R\}$, $C=\langle\square_1,\square_2\rangle$, the two distinct old
classes, and the retained guarded record $(0,L,1,R,=)$ exactly as in
(ARH.8.5). Let $H_0$ be any finite list of literal records, with their
epochs, repetitions and absent replies. Let $Q$ be any finite prefix-free
set of original addresses. Use Assumption 1.3, in particular the complete
accessible input and the same actual original-root register at certified

$$
N\ge\max\bigl(\{1\}\cup\operatorname{epochs}(H_0)\bigr).
\tag{ARH.27.1}
$$

The entire source parameterization is the supplier Theorem 8.2, not an
additional assumption or a new parameterization theorem:

$$
F(y)=\langle\rho(y),y\rangle,\qquad
V=\{y\in\mathcal T:
       r_{\rho^a F(y)}(p)=c\ \text{for every }(a,p,c)\in H_0\},
\qquad U=F[V].
\tag{ARH.27.2}
$$

Here $y$ ranges over all finite nonempty free ordered trees satisfying the
displayed conjunction. The old inequality holds at every such value by
$\kappa(\rho(y))=\kappa(y)+1$; both endpoints of the retained equality
exist. These are consequences already used in (ARH.8.5), not permissions
to discard a possibly false old constraint. The inverse parameter is the
mathematical original subtree $u|_R$. It is not freely accessible data.

Write $s\equiv_h t$ for agreement of all original replies at addresses of
length strictly less than $h$, as in Definition 19.1. Thus agreement
through inclusive depth $b$ is $\equiv_{b+1}$. Put

$$
d=1+\max\bigl(\{0\}\cup\{|p|:(a,p,c)\in H_0\}
                         \cup\{|q|:q\in Q\}\bigr).
\tag{ARH.27.3}
$$

A depth-$d$ pattern records every constructor at depth less than $d$,
stops at each concrete leaf, and places a distinct variable at every
reached depth-$d$ position. Its variables occur once in the pattern.
They range independently over all of $\mathcal T$. For a pattern $t$,
write $\mathcal C(t)$ for its set of finite fillings.

**Proposition 27.2 (literal cylinders with both source inclusions).**
There is an effective finite list $\mathcal L$ of depth-$d$ patterns
such that

$$
V=\coprod_{t\in\mathcal L}\mathcal C(t),\qquad
U=\coprod_{t\in\mathcal L}\{F(t[v]):v:X_t\to\mathcal T\}.
\tag{ARH.27.4}
$$

Every listed pattern has all its finite fillings, without residual
constraints. The displayed maps are bijective when the pattern and its
frontier valuation are included. In particular $U$ is empty exactly when
$\mathcal L$ is empty. Pattern identity has a bounded original-prefix
selector.

Proof. The finite depth-pattern construction is the one in Definition
74.2 of [SLH][SLH], applied to the single parameter tree. Enumerate all its
patterns and, in each, fill every frontier variable by $\alpha$ to get a
finite test tree. Keep the pattern if and only if this test tree, after
applying $F$, satisfies every literal in $H_0$.

This finite test is exact on the whole cylinder. Two fillings of the same
pattern are $\equiv_d$. Lemma 19.2 gives the same agreement after $F$.
The address-locality statement (SLH.74.7) then makes their replies at each
specified epoch and address identical, since $|p|<d$. In particular
arbitrarily large retained epochs do not require deeper original
patterns. The known finite iterates used in the test include all
leaf-sector reach guards. Each occurrence in the history list is tested,
so a repeated incompatible record rejects the pattern and an absent
reply retains its exact meaning.

Every finite $y$ has a unique depth-$d$ pattern and unique frontier
subtrees. If $y\in V$, the test tree of that pattern has the same retained
replies, so the pattern is listed. Conversely every filling of a listed
pattern has all the required replies. This proves both inclusions for
$V$. Apply the supplied bijection (ARH.27.2) to get both inclusions for
$U$, with its complete old row and guarded relation. Recovering $y$ at
original $R$ and its frontier subtrees proves uniqueness. Every pattern
has a finite filling, including the empty valuation of a ground pattern;
therefore the emptiness assertion follows.

The selector consists only of the original replies of $y$ at $|s|<d$,
which are original replies of $u$ at $Rs$. They have physical original
length at most $d$. At a current epoch these are decoded by the paid
literal supplier, not obtained by inspecting a hidden parameter. Distinct
patterns differ at one such reply. This also rules out an unobserved
semantic branch between the cylinders. $\square$

**Definition 27.3 (target descriptions in a cylinder).** If
$Q=\{\varepsilon\}$, its full row is the constant single root-hole row;
this case needs no hole comparison. Otherwise every cut is nonroot.
For each $t\in\mathcal L$, form the normalized source template

$$
F_t=\langle\rho(t),t\rangle
\tag{ARH.27.5}
$$

by distributing $\rho$ through explicit pairs and evaluating its
concrete leaves. Residual occurrences are $x$ or $\rho(x)$ and have
original source depth $d+1$, greater than every cut length. Navigate the
original $Q$, retaining absent cuts as absent, and mask the reached
subtrees in their original lexicographic order. This computes the
reached set $J_t$, a normalized exterior $E_t$ with numbered hole
symbols, and every entire hole value.

Each hole value has one of two descriptions: a known ground tree $g$,
or a tag $(a,s)$ denoting

$$
\rho^a(y|_s),\qquad a\in\{0,1\},
\tag{ARH.27.6}
$$

where $s$ is reached in every $y\in\mathcal C(t)$. For a cut $Rs$, use
$a=0$; for a cut $Ls$ with $s$ originally reached in $y$, use $a=1$.
A ground subpattern is evaluated and described as ground. If navigation
in the left copy passes an original leaf of $y$, the rest is navigation
in that leaf's known one-step image: it either yields a ground hole
value or makes the cut absent. Such a reached position is an original
position of $u=F(y)$, even though it was created in forming the left
copy from $y$. It is never confused with a position born after the
physical entry epoch.

These descriptions are exhaustive because $\rho$ preserves pairing and
acts only on leaves. No navigation can encounter an unresolved
depth-$d$ variable before a cut ends. Thus throughout this cylinder,

$$
\begin{aligned}
I_Q(F(y))&=J_t,&
C_Q(F(t[v]))&=E_t[v],\\
q\sim r&\Longleftrightarrow
        \text{the two described whole hole values are equal}.
\end{aligned}
\tag{ARH.27.7}
$$

Let $O_t$ be the set of frontier variables actually occurring in $E_t$,
including decorated occurrences. The supplied template injectivity of
Lemma 19.2, with the fixed numbered holes treated as constants, gives

$$
E_t[v]=E_t[w]\quad\Longleftrightarrow\quad
v(x)=w(x)\quad\text{for every }x\in O_t.
\tag{ARH.27.8}
$$

Consequently two full rows in one cylinder differ exactly when an
exterior coordinate in (ARH.27.8) differs or one unordered pair of
reached holes changes equality status. This is the entire-row
disagreement equivalence used below. A chosen pair is only a witness
of disagreement, not a replacement target.

## 28. Incomparable underlying positions and the exact finite-pair interface

**Lemma 28.1 (independent subtrees within this full cylinder).** Fix a
listed pattern $t$ and two incomparable reached positions $s,r$ in $y$,
both of length less than $d$. Let $t_s,t_r$ be the subpatterns rooted at
those positions. The possible pairs $(y|_s,y|_r)$, as $y$ ranges over
$\mathcal C(t)$, are exactly

$$
\mathcal C(t_s)\times\mathcal C(t_r).
\tag{ARH.28.1}
$$

Every such pair has an effective finite completion to $\mathcal C(t)$.
Moreover two pairs $(z,w),(z',w')$ with $z\equiv_j z'$ and
$w\equiv_j w'$ admit completions $y,y'$ satisfying $y\equiv_j y'$.

Proof. A subtree of a filling necessarily fills its subpattern. In the
other direction remove the two disjoint subpatterns from $t$, leaving a
context with two distinguished placeholders. Fill its other frontier
variables by $\alpha$, and insert $z,w$ at the placeholders. Since
$s,r$ are incomparable, their frontier variable sets are disjoint, and
this operation gives precisely the specified subtrees and a filling of
$t$. It is finite and effective. Apply the same context and the same
other fillings to $z',w'$. Any original address either stays in the fixed
context or enters one placeholder and uses a suffix no longer than the
whole address. Agreement at relative lengths less than $j$ therefore
gives $y\equiv_j y'$, including absence below a leaf. $\square$

This product statement is confined to disjoint original subtrees of the
single linear pattern. The old pair $(\rho(y),y)$ remains coupled
throughout. In particular (ARH.28.1) is not a product approximation of
that acquired graph.

**Proposition 28.2 (complete local test from the synchronous supplier).**
For fixed $a,b\in\{0,1\}$ and the positions of Lemma 28.1, there is a
terminating exact decision of finite-prefix determination, on
$\mathcal C(t)$, of the bit

$$
e(y)=[\rho^a(y|_s)=\rho^b(y|_r)].
\tag{ARH.28.2}
$$

A positive answer supplies an integer $h$ such that
$y\equiv_h y'$ implies $e(y)=e(y')$ throughout the cylinder. A negative
answer supplies, for every requested $j$, finite $y,y'\in\mathcal C(t)$
with $y\equiv_j y'$ and opposite values of $e$.

Proof. This is an application of Lemma 21.1 and Theorem 13.1 to the
following exact four-coordinate relation, not a new automata closure:

$$
\begin{aligned}
\mathcal B_{s,r}=\{(z,w,z',w'):\;&
 z,z'\in\mathcal C(t_s),\quad w,w'\in\mathcal C(t_r),\\
&[\rho^a z=\rho^b w]\mathbin{\mathsf{xor}}
 [\rho^a z'=\rho^b w']\}.
\end{aligned}
\tag{ARH.28.3}
$$

A cylinder is specified by finitely many coordinate-prefix replies.
The two equality atoms are exactly fixed-power aligned atoms of
(CE.20.3). Thus Lemma 21.1 constructs a finite bottom-up automaton on
valid padded convolutions of four nonempty finite trees for precisely
(ARH.28.3). Complement and xor are relative to valid finite coordinates.
There is no shifted-constructor graph inside this automaton.

Use Theorem 13.1 with $k=2$, pairing the first two coordinates with the
last two. It computes its productive diagonal-prefix fixed set. If the
accepting intersection is empty, it supplies a finite $j_0$ for which
no member of (ARH.28.3) has both paired agreements $\equiv_{j_0}$.
Set

$$
h=\max(|s|,|r|)+j_0.
\tag{ARH.28.4}
$$

Agreement $y\equiv_h y'$ restricts to those two agreements, so their
equality statuses coincide. This proves the positive claim.

If the accepting intersection is nonempty, the same supplier constructs,
for each $j$, a member of (ARH.28.3) with the two paired agreements
$\equiv_j$. All four coordinates are finite productive witnesses.
Complete them by Lemma 28.1, using the same other fillings. The resulting
$y,y'$ have the required agreement and opposite statuses. Conversely,
any two cylinder trees with opposite statuses project to (ARH.28.3).
The product correspondence proves that no spurious local negative
witness was introduced by this projection.

The state set is finite and the supplied decreasing sequence stabilizes;
each requested witness is a finite productive completion. Hence this
test stops in both cases. Neither testing a fixed depth nor admitting an
infinite solution has replaced the negative stopping argument. $\square$

## 29. Nested comparisons and finite atomic witnesses

**Lemma 29.1 (the exact nested comparison).** Let $z\in\mathcal T$,
let $p\ne\varepsilon$ be originally reached in $z$, and let
$a,b\in\{0,1\}$. Then

$$
\rho^a(z)=\rho^b(z|_p)
\quad\Longleftrightarrow\quad
a=0,\ b=1,\ p=L,\quad z=T_k\text{ for some }k\ge2.
\tag{ARH.29.1}
$$

Proof. If $a=b$, injectivity reduces the equation to equality of a finite
tree and its proper subtree, which finite node count excludes. If
$a=1,b=0$, the number of nodes of $\rho(z)$ is at least the number of
nodes of $z$, while a proper subtree has fewer. This excludes that case.
Node monotonicity follows directly from the two actual leaf images and
preservation of pairing.

It remains to consider $z=\rho(z|_p)$. Because $p$ is an original reached
position, original-address transport gives

$$
(\rho z)|_p=\rho(z|_p)=z.
\tag{ARH.29.2}
$$

Both endpoints of the predicate $(0,\varepsilon,1,p,=)$ on this very
finite tree $z$ therefore exist. Apply the source classification in
Theorem 4.2 to precisely this predicate: it forces $1=w(p)$ and
$z=T_k$ with $k\ge1$. Positive letter weights give $p=L$. Original
reach of $L$ in $z$, an additional hypothesis retained here, then gives
$k\ge2$. Conversely, for $k\ge2$, $T_k|_L=T_{k-1}$, and
$\rho(T_{k-1})=T_k$. This proves the converse with the original guard.

The application of Theorem 4.2 has been supplied with its whole-root,
proper-descendant equality (ARH.29.2), derived under the target equality
being classified. It is not applied to the old-child record of
(ARH.8.5), and does not assert that all sources in that graph have a
root certificate. Using $z$ as a mathematical argument neither reroots
the physical register nor acquires a comparison. $\square$

**Proposition 29.2 (exact cylinder decision for the remaining nested bit).**
Let $s$ be a reached position of a depth-$d$ pattern $t$, with
$m=d-|s|\ge1$, and suppose $sL$ is reached throughout $\mathcal C(t)$.
On this cylinder consider

$$
e_s(y)=[y|_s=\rho(y|_{sL})].
\tag{ARH.29.3}
$$

If the subpattern $t_s$ contains a concrete leaf, $e_s$ has an effective
finite-prefix bound. If it contains no concrete leaf, $e_s$ has finite
positive and negative witnesses agreeing to every requested finite
depth in the whole cylinder. Both alternatives are decidable.

Proof. Lemma 29.1 identifies the positive values of $z=y|_s$ exactly as
$T_k$, $k\ge2$, that fill $t_s$. The subpattern records every relative
level below $m$ and has variables only at level $m$.

For $k\ge2m+2$, every relative address of length less than $m$ in $T_k$
is reached and has reply branch. Indeed its weight is at most
$2(m-1)$, and the guarded formula (ARH.4.3) gives reach and residual index
at least two. If $t_s$ contains a concrete leaf, no such $T_k$ can fill
it. Compute the finite set

$$
A_s=\{T_k:2\le k<2m+2,\ T_k\in\mathcal C(t_s)\}.
\tag{ARH.29.4}
$$

Membership in this set is exactly the bit in question on the cylinder.
Matching all replies of a given finite tree $g$ through its height
forces the whole tree, by its concrete leaves and pairing. Thus, if
$A_s\ne\varnothing$, the effective choice

$$
h_s=|s|+1+\max_{g\in A_s}\operatorname{ht}(g)
\tag{ARH.29.5}
$$

makes $y\equiv_{h_s}y'$ preserve membership in $A_s$. If $A_s$ is empty
the bit is constantly false and take $h_s=0$. This proves the first
alternative without bounding other subtrees of $y$.

If $t_s$ has no concrete leaf, it is the complete pairing pattern to
depth $m$, with distinct free frontier variables. Fix any requested
inclusive depth $b$ and set

$$
K=2(d+b+3),\qquad z=T_K.
\tag{ARH.29.6}
$$

The tree $z$ fills $t_s$. Its rightmost leaf, at $R^{K/2}$, is $\alpha$,
by (ARH.4.3); this depth is greater than both $m$ and $b$. Change only
that leaf to $\beta$, giving a different finite tree $z'$. It still
fills $t_s$, and $z\equiv_{b+1}z'$. Its whole left child is unchanged,
so

$$
\rho(z'|_L)=\rho(z|_L)=z\ne z'.
\tag{ARH.29.7}
$$

Consequently $z$ has positive status and $z'$ negative status. Fill the
rest of $t$ identically by $\alpha$ at the frontier variables outside
$s$, and insert $z,z'$ respectively at $s$. The same context argument
as in Lemma 28.1 gives two finite cylinder trees with agreement through
depth $b$ and opposite bits. Every $b$ has such a construction; it uses
finite trees, not the infinite all-branch limit. $\square$

**Definition 29.3 (the total hole-pair test).** For any two reached holes
in a cylinder, use their ground values or tags from Definition 27.3.
The following finite cases decide their equality-bit determination.

1. Two ground values have constant status. For one ground $g$ and one
   tag $(a,s)$, apply the supplied partial inverse $\delta^a$ to $g$.
   Failure makes equality constantly false. Success gives a finite $c$
   and exactly $y|_s=c$, determined by
   $h=|s|+\operatorname{ht}(c)+1$.
2. For two tags $(a,s),(b,r)$ with $s=r$, equality is constant: true
   if $a=b$, false otherwise by the clock.
3. For incomparable $s,r$, use Proposition 28.2.
4. Otherwise orient the positions as $r=sp$ with
   $p\ne\varepsilon$, interchanging the two tags if necessary. The
   equation has precisely the form of Lemma 29.1. It is constantly
   false unless $a=0,b=1,p=L$. In that one case use Proposition 29.2.

Return the displayed bound in a positive case and bound zero for a
constant status. In a negative case retain the effective finite-witness
construction. Ground matching in item 1 requires no assumption that the
ground value is feasible; if it is infeasible the same bound still
suffices. In item 4 the original reach of $p$ follows from the two tags
and is not dropped. Every pair of finite words is equal, incomparable,
or properly nested in one orientation, so these cases exhaust every
original hole pair. There is no unsupported result.

## 30. The terminating full-domain criterion

**Definition 30.1 (graph-row decision).** Compute $\mathcal L$ and every
target description of §27. If the list is empty, return YES with an
explicit empty-domain flag. If $Q=\{\varepsilon\}$, return YES with
inclusive original bound $H=0$. Otherwise require, on every listed
pattern, both of the following:

- $O_t=\varnothing$.
- Every unordered pair of reached holes passes the positive branch of
  Definition 29.3.

If either requirement fails, return NO, retaining that pattern and its
failed exterior or hole-pair witness data. If all pass, let $h_{t,qr}$
be the positive bounds from Definition 29.3 and return YES with

$$
H=\max\bigl(\{d\}\cup
     \{h_{t,qr}:t\in\mathcal L,\ \{q,r\}\subseteq J_t,\ q\ne r\}\bigr).
\tag{ARH.30.1}
$$

An empty set of hole pairs contributes no bound. This definition is a
finite algorithm on the original common input, not a source-size cutoff.

**Theorem 30.2 (complete arbitrary-cut decision on the entire graph).**
For every finite $H_0$ and every finite prefix-free original $Q$ in
Definition 27.1, the algorithm of Definition 30.1 terminates. Its answer
is YES if and only if

$$
\exists H\ge0\ \ \forall u,u'\in U,\quad
 \bigl[\forall p,\ |p|\le H\Longrightarrow r_u(p)=r_{u'}(p)\bigr]
 \Longrightarrow R_Q(u)=R_Q(u').
\tag{ARH.30.2}
$$

For nonempty $U$, YES supplies the computed sufficient original prefix.
NO supplies, for every requested inclusive original depth $b$, an
effective pair of finite sources in that same entire retained fiber
which agree at every original address of length at most $b$ and have
different entire original $Q$ rows. All original repetitions, absences,
old distinctness, endpoint guards and coupling are preserved. No
eligibility restriction on $Q$ is imposed.

Proof. The pattern list is finite. Ground evaluation, finite partial
inversion, word-prefix comparisons and the finite enumeration (ARH.29.4)
terminate. The only saturation is the finite-state terminating
Theorem 13.1 application in Proposition 28.2. Proposition 29.2 has a
finite syntactic branch test. Thus every branch of the decision
terminates, independently of the size of any unknown source.

Suppose the answer is YES and $U$ is nonempty. The root-cut case is
immediate from the definition of a whole row. In the other cases take
$u=F(y),u'=F(y')$ satisfying the antecedent of (ARH.30.2) with the
computed $H$. Every relative address $s$ of length less than $H$ has
original address $Rs$ of length at most $H$. Hence $y\equiv_H y'$.
Since $H\ge d$, Proposition 27.2 puts them in the same listed pattern
$t$, with their own finite valuations $v,w$.

Its reached set and numbering agree by (ARH.27.7). Its exterior is
constant since $O_t$ is empty. For every hole pair,
$H\ge h_{t,qr}$, so the exact pair test proves equal equality status on
$y,y'$. Agreement of all those statuses is exactly agreement of the
whole partition on the fixed finite reached set. The entire rows are
therefore equal. This is a simultaneous statement about the two actual
sources; separately chosen equality witnesses have not been assembled
into a fictitious partition. It proves YES implies (ARH.30.2).

Now suppose a listed pattern fails the exterior requirement. Choose
$x\in O_t$. For any supplied $b$, let $z$ be the perfect finite binary
tree of height $b+1$ with all leaves $\alpha$, and let $z'$ change one
depth-$b+1$ leaf to $\beta$. They are distinct and agree at every
relative address of length at most $b$. Use $z,z'$ for $x$ in two
valuations, and the same $\alpha$ for every other frontier variable.
All valuations are permitted by (ARH.27.4). Filling the fixed pattern
preserves $\equiv_{b+1}$, and Lemma 19.2 preserves it after $F$.
The two resulting finite original sources thus agree through depth
$b$. Their exteriors differ by (ARH.27.8), because $\rho$ is injective
as well as a bare variable being injective. Their entire rows differ.

The remaining negative case is a failed pair test. A ground comparison,
an equal-position comparison and a constantly false nested comparison
cannot fail. For a failed incomparable comparison, apply Proposition
28.2 with $j=b+1$ and use its two finite full-cylinder completions.
For the exceptional failed nested comparison, use the explicit
construction (ARH.29.6)–(ARH.29.7). In both cases this gives finite
$y,y'\in\mathcal C(t)$ with $y\equiv_{b+1}y'$ and opposite truth values
for the chosen complete-hole equality. Apply $F$ to both. Locality gives
original agreement through depth $b$, while (ARH.27.7) makes the two
entire partitions, and hence entire rows, different.

Every constructed source belongs to the same $U$ by both inclusions
of (ARH.27.4). In particular the left component is recomputed as
$\rho(y)$ after each change; it is never varied independently or kept
as an incompatible old value. The clock preserves distinct old
children for every new $y$. Literal repetitions and all original
guards have already been imposed on the whole cylinder. Finite
completion cannot invalidate them. These constructions are effective
for every requested finite $b$ and disprove (ARH.30.2) at every bound.

The two negative cases exhaust every way the algorithm returns NO,
so they prove (ARH.30.2) implies YES as well. With $\mathcal L$ empty,
Proposition 27.2 proves logical emptiness and (ARH.30.2) is vacuously
true. Reporting that flag does not claim a nonempty acquired entry.
One may take $H=0$ in this case. $\square$

For $Q=\varnothing$, the exterior is all of $F_t$; every free frontier
variable is visible. The decision is consequently YES exactly when
every listed pattern is ground, equivalently when $U$ is finite.
This conclusion includes the empty logical fiber. For a root cut the
row is constant even on an infinite fiber. Cuts that are absent in one
pattern and reached in another are distinguished by the finite selector;
an absent cut creates no hole in its own pattern. These conclusions
use the original cuts, without replacing them by a level cut.

## 31. The inherited paid consumer and the retained resource boundary

**Corollary 31.1 (lawful static whole-row recovery at every allowed epoch).**
On every nonempty acquired input of Definition 27.1, the following
conditions are equivalent:

1. The algorithm of Theorem 30.2 returns YES.
2. For every permitted certified $N$, there exist a deterministic
   effective source-total static full-row service $A_N$ and an integer
   $K_N<\infty$ such that $A_N$ uses at most $K_N$ new raw reads on
   every $u\in U$.
3. For some permitted certified $N$, there exist a deterministic
   effective source-total serial full-row service $A$ and an integer
   $K<\infty$ such that $A$ uses at most $K$ new raw reads on every
   $u\in U$, allowing real forward updates on the same register.

Each service and its bound use only the common retained input and task;
the bound in each predicate is uniform over the entire $U$. Moreover,
on YES the static services can be constructed effectively from the
computed sufficient inclusive original depth $H$, with one raw bound
$K_0$ valid simultaneously for every permitted $N$:

$$
K_0=2(2^{H+1}-1),\qquad
\max|p_{\mathrm{physical}}|\le H+\lceil N/2\rceil.
\tag{ARH.31.1}
$$

The bound on raw calls is independent of $N$. A root-cut input can
instead halt with its known row and zero new reads. A NO answer excludes
a uniform finite raw bound for every permitted static or serial service.

Proof. Apply the existing bridge (ARH.2.3) to the exact $U$ of
(ARH.27.2). Its common complete state, decidable finite-candidate
membership, four literal replies, original-address locality and
source-totality hypotheses are precisely those of Definition 27.1
and Assumption 1.3. Theorem 30.2 supplies the previously missing
effective bound or all-depth obstruction; the bridge itself is reused.

Explicitly, at the actual static epoch $N$, use [SLH, Theorem 2.2][SLH]
to recover all original replies at $|p|\le H$. This gives (ARH.31.1).
Each decoder request is an actual original-root address, and every
actual repeated call is paid. The acquired evidence is the actual
$N$-epoch address/reply list, not fabricated old events.

Enumerate finite original trees in an effective size-and-encoding order.
Test each candidate against the complete old row, every retained literal,
both relation guards, the complete acquired equality and the recovered
original prefix. All these tests on a supplied finite candidate are
decidable. The actual source guarantees a successful candidate, so this
local search terminates on every admitted source. Compute its entire
original $R_Q$ and output it, then enter absorbing Halt. Theorem 30.2
makes the output common to the whole prefix-conditioned fiber; the
candidate is not claimed to be the actual source. The consumer neither
queries an unknown equality nor reads an unobserved chart or code.

The bridge's converse covers all allowed effective serial services,
including reply-dependent finite updates and unbounded a priori physical
addresses. Its finite reachable reply tree under a uniform raw bound,
together with original-address locality, would give a finite determining
original prefix. The NO witnesses contradict that conclusion. This
reuse establishes equivalence of uniformly raw-bounded service existence,
not equality of minimum raw prices. $\square$

Source-totality without a uniform read bound has a different meaning.
The paid original-tree traversal used in [SCR, Theorem 6.1][GRAPH-SCR]
works on every finite source: at the fixed actual epoch $N$, decode the
original root reply with [SLH, Theorem 2.2][SLH], and decode both original
children only after a decoded branch. Each original node costs at most
two actual current-register reads. The original tree is finite, so this
procedure terminates, reconstructs it, computes the entire $R_Q$, and
enters absorbing Halt. It uses at most $2|\operatorname{Pos}(u)|$ new
reads on that source, with no uniform bound asserted over $U$.
Restricting this all-tree procedure to the present acquired fiber is
lawful and preserves every retained predicate; it adds no inverse,
reroot, equality, identity or timing port.

For example, with $H_0=\varnothing$ and $Q=\varnothing$, the full graph
has no determining finite prefix by Theorem 30.2: its concrete exterior
contains the entire source and its cylinder list has a nonground pattern.
Explicitly, for each inclusive $b$, take a perfect all-$\alpha$ tree
$y$ of height $b+1$ and change one deepest leaf to $\beta$ to obtain
$y'$. The finite sources $F(y),F(y')$ lie in that same full fiber, agree
through $b$ by Lemma 19.2, and have different empty-cut rows. Nevertheless
the preceding source-total static traversal works at every permitted
$N$. Thus NO rules out exactly the uniformly raw-bounded service classes
in items 2–3; it does not rule out source-total recovery with an unbounded
source-dependent read count. This distinction uses the existing traversal
and prefix suppliers and adds no minimum-price or new traversal theorem.

The empty-domain flag has only a logical interpretation: immediate
output of any fixed row, for example $R_Q(\alpha)$, has vacuous
correctness with zero calls. It is not an actual acquired-state
realization.

The computation of patterns, automata, finite trees and installed
consumer code is effective ordinary mathematics. It supplies no
implemented solver, practical complexity estimate, uniform running-time
guarantee or physical acquisition procedure beyond the existing
conditional producer contract. Semantic projections to $y$ and its
subtrees are not reset, reroot, clone, inverse, identity, equality or
code-inspection operations. Only paid literal reads occur in the
positive consumer; no new update is needed.

Raw calls, actual updates, physical address length and radius, address
generation and transmission, certified versions, working storage,
retention, local work, labels, bits, fees, installation, acquisition,
entry, archives, output, clocks, precision, field and reference resources,
and total physical resources remain separate obligations. For the
displayed consumer the actual post-entry update count is zero and the
address-length sum is at most $K_0(H+\lceil N/2\rceil)$; these are
sufficient bounds, not joint optima or prices for the other coordinates.

In particular outputting $r=R_Q(u)$ does not erase the old relation,
$H_0$, the actual new replies or other accessible fields. A separately
supplied complete-successor retention operation, with its own payment
and state correspondence, is still necessary. If its whole accessible
source-bearing content is exactly a recoverable encoding of $r$ and
common data, the conditional new fiber is $U\cap R_Q^{-1}(r)$, by the
existing complete-cut contract. Remaining accessible information imposes
its further intersections. Absorbing Halt does not supply another entry.

## 32. Exact reuse, ordinary authorship and the unresolved larger domains

The source-relative mathematical increment is Theorem 30.2 on every
literal refinement of (ARH.8.5) and every original finite prefix-free
$Q$. It uses the independent-subtree extension in §28 and the exhaustive
nested comparison in §29 to discharge every target comparison without
a family-recognition failure. The source, full exterior and full
partition correspondences, positive bound and finite all-depth negative
constructions are part of that result. Graph parameterization, aligned
automata, the productive-prefix test and the general operational bridge
are expressly reused and receive no new-theorem credit here.

The overlap and hypothesis boundaries are the following.

- Sections 1–3 and Theorem 8.2 of this volume supply the acquired graph,
  complete access contract and inherited service equivalence. Sections
  4–6 classify their actual root-to-proper-descendant certificate
  fragment. Lemma 29.1 applies that classification only after deriving
  its exact guarded predicate on the finite tree being compared.
  It does not give the full graph an unretained root certificate.
- Sections 10–18 decide the synchronous family with both domain and
  target eligibility. In particular Proposition 15.1 already covers the
  present old cut and equality record when $Q$ is on one level, with
  arbitrary $H_0$. Sections 19–25 additionally cover each entire
  presentation accepted by the constructor-elimination recognizer,
  again including its target requirement. Those admitted cases are
  existing supply. Rejection by either recognizer is never used here
  as NO. Definition 29.3 instead exhausts every pair of actual underlying
  positions, and Theorem 30.2 has no recognizer premise.
- [SLH, §§74–75][SLH] supplies the full literal-only old-row problem,
  the finite pattern method and the address-locality/paid-decoder
  interfaces. [SCR, §§1–10][GRAPH-SCR] supplies its literal-only exact
  complete-row prices and sharp common-epoch normalization.
  [JRF, §§1–10][GRAPH-JRF] supplies its own literal-only joint frontier
  and separate same-run weighted prices. Their exact optimization
  conclusions are not imported after discarding the acquired graph
  relation. This appendix computes a sufficient raw bound and makes
  no new minimum-price claim.
- [AtomicBlockConjugacy, §§2–6][GRAPH-ABC] supplies canonical codes,
  source and whole-row correspondences, and opaque-port semantics.
  Its §§7–8 distinguish a uniform normal-domain interpretation from
  a fixed-prefix decision and from unbounded-prefix stopping.
  [AtomicTermPowerObstruction, Definition 1.2, Corollaries 4.2–4.4
  and Proposition 5.2][GRAPH-TPO] supplies a language-specific exclusion
  of that all-shape normal-domain formula and the total ambient
  canonicalization graph. Its stated language has four sorts, pointwise
  inner base formulas and no arbitrary leaf-address rank selector.
  That exclusion does not supply a native same-fiber counterpair or
  a native service-impossibility theorem. Neither the excluded premise
  nor any ambient term-power decision or hidden code access is used
  in Theorem 30.2; the present automata run on actual finite trees.
- [AcquiredOrbitResourceFrontier, Assumption 1.1 and §§2–5][GRAPH-AOF]
  requires a recognized acquired whole-root/proper-descendant
  certificate. Its finite/cofinite orbit domain and attained resource
  optima do not apply to the arbitrary old-child graph in (ARH.27.2).
  Its source-specific resource theorem is not duplicated.
- Section 26, Applications 26.1–26.9, supplies only its stated
  three-hole feedback application of the orbit results. Its exact
  record (CS.26.1), whole-source correspondence (CS.26.3), and
  uniformly bounded consumer in Application 26.8 retain their scopes.
  This reuse-only source does not replace the two-hole graph input
  of Definition 27.1 or contribute a new theorem to it.
- The finite ranked-tree automata background is
  literature-attested in [TATA, Theorems 1.3.1 and 1.7.4][GRAPH-TATA]:
  effective Boolean closure on finite ranked alphabets and
  productive-state emptiness. The exact interpreted fixed-power
  graphs, valid padding, coordinate-prefix restrictions and
  all-depth diagonal stopping rule used here are the already supplied
  Lemma 21.1 and Theorem 13.1. None of these is a new general automata
  theorem in this appendix.
- [Kuncak–Rinard, Theorem 56, Corollary 57, Theorem 58 and §6.6][KR-GRAPH]
  decides its specified term-power language over a decidable base,
  with the semantics of Figures 9–11. Its element-selection discussion
  separates a stronger language. Neither is invoked as a decision of
  normal-code membership or of the unbounded original-prefix question.
  The present finite-pair proof does not require such an interpretation.

The bounded project comparison uses the full source contracts
ARH §§1–25, SLH §§74–75, SCR, JRF, AtomicBlockConjugacy and
AcquiredOrbitResourceFrontier in the immutable catalogue at revision
[ae1314adbd58cecf7e0c2f29cd08bd5e552276fb][GRAPH-PIN]. Those ARH
§§1–25 also agree with the target revision
[fee3e2b8ff28d5048af2e03cfd83ef522a30365b][GRAPH-BASE].
The comparison includes the independent Section 26 at
[28cc5e33857d4969363b213e6f8c4269fd012972][GRAPH-PUBLIC]
and the stated AtomicTermPowerObstruction interface. The primary
comparison is limited to the stated TATA results and the stated
Kuncak–Rinard language and decision boundaries. No exact full-graph,
arbitrary-$H_0,Q$ decision is supplied by those inspected interfaces.
This bounded source comparison is not a global nonexistence, novelty
or priority claim.

**Provenance and evidence boundary.** This appendix is independently
authored ordinary pure theory by one external CLI scientific author,
with repository priors exposed. The author chooses and is responsible
for the displayed mathematical construction and proofs; supplied source
texts are fallible theorem suppliers. There is no claim that their
publication or formal metadata freshly certifies this application.
The formal-thinking and theory-volume-template conventions are used
within the pure-theory scope. No delegated author, Oracle call,
same-round peer result or independent scientific review supplies these
proofs. This manuscript is not self-approval. There is no new Lean,
kernel, Reg, Blueprint, implementation or physical validation claim.

Theorem 30.2 settles the stated ordinary decision problem only on the
entire one-step graph with arbitrary mixed literal refinement. General
guarded coupled relation histories remain outside its conclusion.
Minimum raw prices on these relational domains, joint optima,
complete-successor retention, physical realization, uniform time,
source acquisition and stochastic $j_c$ are not established here.
The original source/history/control/native/continuum/quantum/field/
reference/resource and sustained programme obligations remain active.
Neither this mathematical handoff nor later local acceptance completes
that whole objective.

[GRAPH-SCR]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_COMPLETE_ROW_PRICE.md
[GRAPH-JRF]: RECURSIVE_RELATIONAL_OBSERVATION_SERIAL_JOINT_RESOURCE_FRONTIER.md
[GRAPH-ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[GRAPH-AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[GRAPH-TPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_TERM_POWER_OBSTRUCTION.md
[GRAPH-PUBLIC]: https://github.com/the-omega-institute/trureturing/blob/28cc5e33857d4969363b213e6f8c4269fd012972/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[GRAPH-TATA]: https://inria.hal.science/hal-03367725v1/document
[KR-GRAPH]: https://arxiv.org/html/cs/0408015v1
[GRAPH-PIN]: https://github.com/the-omega-institute/trureturing/tree/ae1314adbd58cecf7e0c2f29cd08bd5e552276fb
[GRAPH-BASE]: https://github.com/the-omega-institute/trureturing/tree/fee3e2b8ff28d5048af2e03cfd83ef522a30365b

## 追加锚（本行以下为增补区）
