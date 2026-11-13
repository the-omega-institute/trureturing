# Native alpha recut zero boundary: arbitrary-budget complete-fiber absorption

## Inherited source contract and notation

**Source convention.** NARC denotes [Native alpha recut memory
continuation: exact fixed-reference reading](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md).
A reference prefixed by NARC names a definition, assumption, theorem or
section in that volume. Equation references of the form (NARC.x.y)
likewise retain that source's numbering. The local numbered statements
are Definition 1.1, Lemma 1.2 and Theorem 1.3; local equation tags use
NARZ. The parameters below are the same $q,k,a,b,\lambda,z,Z$ and
$e$ as in NARC, without a change of source offsets or indices.

**Native source and causal entry (NARC Assumptions 5.1 and 9.1).**
The sources are finite nonempty ordered trees with distinct leaf labels
$\alpha,\beta$ and literal pairing. The homomorphic substitution and
its iterates are

$$
\begin{aligned}
\rho\alpha&=\beta,&\rho\beta&=\langle\beta,\alpha\rangle,&
\rho\langle s,t\rangle&=\langle\rho s,\rho t\rangle,\\
T_n&=\rho^n\alpha,&T_0&=\alpha,&T_1&=\beta,\\
T_{n+2}&=\langle T_{n+1},T_n\rangle.&&&
\end{aligned}
$$

Fix public integers $q\ge1$, $k\ge0$ and a public lag convention
$\lambda\in\{0,1\}$. Every integer pair $0\le a,b<q$ is an
allowed original $X_{a,b}=\langle T_a,T_{q+b}\rangle$; independence
here imposes no probability distribution. The original offsets stay
$0,q$. The complete original empty-cut row is genuinely acquired.
The supplied clock $c(T_n)=n$ parses acquired literals, so that this
row supplies $a=c(T_a)$ and $b=c(T_{q+b})-q$. A deterministic
encoder exports only $e(a,b)$, with exactly $q$ attained labels,
before the future cut and lag are known. It discards the row, the
coordinates and every other source-bearing field. The finite encoder
table may be public and common to every source; a source-dependent
table selection or retained origin is not an extra channel.

The same fixed original undergoes its own $\ell\ge\lambda$
substitutions, with integer lag $\ell$, giving
$Y(a,b,\ell)=\langle T_{a+\ell},T_{q+b+\ell}\rangle$.
The later complete row is genuinely acquired at one of the two
singleton cuts. Write $V=R$ for visible right slot and cut $\{L\}$,
and $V=L$ for visible left slot and cut $\{R\}$. A complete row
retains every exterior label and bracket, the reached hole and its
whole singleton partition; it supplies no hidden-visible comparison.
The decoder receives this row, $V$ and the exported label and returns
$\ell$. Its deterministic next request or halt may depend on that
entry, public controls and earlier actual replies. Each query is a
fully materialized finite word in $L,R$ at the original root of this
same stationary current tree. No update occurs during capture or
reading. Each submission, including a repeat or the empty word, costs
one chronological call. Local computation must terminate on every
promised input. There is no age, subtree, epoch, old-source or
hidden-visible comparison oracle, fixed finite Moore restriction or
uniform address bound in this contract.

**Entire indexed fibers (NARC Theorem 5.2).** For an attained label
$\gamma$, write $C_\gamma=e^{-1}(\gamma)$ and $d(a,b)=a-b$.
For integer normalized acquired clock $z\ge\lambda$, the entire
rows and their exact compatible fibers in (NARC.5.3)--(NARC.5.6) are

$$
\begin{aligned}
\mathcal R^R_z&=
 \bigl(\langle\square_L,T_{q+z}\rangle,\{\{L\}\}\bigr),\\
F_R(C_\gamma,z,\lambda)&=\{(a,b)\in C_\gamma:b\le z-\lambda\},&
n_R(a,b)&=z+a-b,&\ell_R(a,b)&=z-b,\\
\mathcal R^L_z&=
 \bigl(\langle T_z,\square_R\rangle,\{\{R\}\}\bigr),\\
F_L(C_\gamma,z,\lambda)&=\{(a,b)\in C_\gamma:a\le z-\lambda\},&
n_L(a,b)&=q+z-a+b,&\ell_L(a,b)&=z-a.
\end{aligned}
$$

The target coordinate is $b$ on right visibility and $a$ on left
visibility. A terminal common target $v$ returns lag $z-v$.
Every compatible index is realized by its own fixed original and its
indicated legal continuation, with equality of the entire acquired
row. Histories are not spliced. After an adaptive transcript the
support contains every index producing all preceding actual replies,
including the actual original. Equal ages or repeated target values
do not identify indices. Root and visible-prefixed requests have
constant replies on this whole input fiber; hidden-prefixed requests
have exactly the relative replies on $T_{n_R}$ or $T_{n_L}$.
Zero calls suffice exactly when the target is constant on the
nonempty input fiber.

**Actual replies (NARC Definition 5.3).** Absence is $\bot$ and
branch is $\mathsf b$. A constructor Read reports the label or
branch at the end of an existing address, and absence if a nonempty
suffix remains at a leaf. Every finite relative word has one of the
following supplied response functions on nonnegative integer ages,
as in (NARC.5.7):

$$
\begin{array}{c|cccc}
 &\bot&\alpha&\beta&\mathsf b\\ \hline
E&\text{never}&n=0&n=1&n\ge2\\
P_t\ (t\ge2)&n<t&n=t&n=t+1&n>t+1\\
S_t\ (t\ge2)&n<t&\text{never}&n=t&n>t.
\end{array}
$$

The $S_t$ reply is obtained from the actual $P_t$ reply by
$\bot\mapsto\bot$, $\alpha\mapsto\beta$ and
$\beta,\mathsf b\mapsto\mathsf b$. There is no native $P_1$.
The literal representatives and the paid hidden-slot prefixes are
those specified in Definition 1.1 below.

**Finite certificates (NARC Definition 10.1 and Theorem 10.2).**
An indexed state $((n_i,v_i))_{i\in I}$ has finite index set $I$
and integer ages $n_i\ge0$. Let $I_{A,r}$ retain exactly every
index with actual reply $r$ to $A$, keeping its age and target.
Use the inherited menu and predicate (NARC.10.1)--(NARC.10.2):

$$
\begin{aligned}
\mathcal M_q&=\{E,P_2,\ldots,P_{3q+1}\},\\
D_0(I)&\ \Longleftrightarrow\ \text{the target is constant on }I,\\
D_{j+1}(I)&\ \Longleftrightarrow\
 \text{the target is constant on }I\quad\text{or}\quad
 \exists A\in\mathcal M_q\ \forall r\in\{\bot,\alpha,\beta,\mathsf b\},
 \ D_j(I_{A,r}).
\end{aligned}
$$

Empty states are vacuous. A constant-target state halts; the other
alternative supplies an actual request with its adaptive reply
subtrees. This is the inherited depth-at-most-$j$ target-separation
predicate, with actual reply partitions and all indices retained.
Put $Z=q+1$. The full reference states of (NARC.10.3) and complete
boundary states of (NARC.10.4) are

$$
\begin{aligned}
S_R(\gamma)&=\bigl((Z+a-b,b)\bigr)_{(a,b)\in C_\gamma},\\
S_L(\gamma)&=\bigl((q+Z-a+b,a)\bigr)_{(a,b)\in C_\gamma},\\
S_0(z)&=\bigl((z+a-b,b)\bigr)_
 {\substack{(a,b)\in C_{e(0,z)}\\b\le z}},\qquad 0\le z<q.
\end{aligned}
$$

Both reference states are whole fibers at acquired clock $Z$; their
ages are at least two. Each $S_0(z)$ is the entire right-visible
fiber at $(e(0,z),\mathcal R^R_z)$ for $\lambda=0$, retaining its
positive-age alternatives as well as its age-zero origin.
NARC Theorem 10.2 identifies both-cut service at every positive lag with
$D_k$ on all full reference states, and both-cut service at every
nonnegative lag with those tests plus all complete boundary tests.
Its finite menu bounds certificate queries, not runtime addresses
at unbounded lags. The collision obstruction in NARC Theorem 9.2
supplies injectivity of $d$ on a readable class.

For an arbitrary integer $s$, the inherited algebraic partition
(NARC.10.5) is

$$
\widehat P_s(n)=
\begin{cases}
\bot,&n<s,\\
\alpha,&n=s,\\
\beta,&n=s+1,\\
\mathsf b,&n\ge s+2.
\end{cases}
$$

It is a partition to be simulated with actual native requests,
not an additional query. All parameter substitutions below use
these same source states, targets and histories.

## 1. Arbitrary-budget absorption of complete zero-boundary tests

**Definition 1.1 (indexed translation and the inherited native contract).**
Keep NARC Assumption 9.1 with public integers $q\ge1$ and $k\ge0$.
The actual originals are $X_{a,b}=\langle T_a,T_{q+b}\rangle$,
$0\le a,b<q$, with their unchanged offsets $0,q$. The encoder
exports exactly $q$ attained labels from the genuinely acquired original
row before the future cut and lag, and discards every other
source-bearing field. Reuse the entire acquired rows, complete fibers,
targets and same-original histories of NARC Theorem 5.2, and the full
reference states at $Z=q+1$ in (NARC.10.3). The finite certificate
predicate is exactly $D_k$ of NARC Definition 10.1, with menu
$\mathcal M_q=\{E,P_2,\ldots,P_{3q+1}\}$.

For the translation below, a reference state is a finite indexed family
$((N_i,v_i))_{i\in I}$ with $N_i\ge2$. A native target tree is a
finite tree whose requests have the actual $E/P/S$ response functions
of NARC Definition 5.3 and whose nonempty leaves have a constant target.
Its depth counts paid requests. Choose any public subset $J\subseteq I$
and any integer $\Delta$ with $n_i=N_i+\Delta\ge0$ for every
$i\in J$. Translation keeps the indices and their targets $v_i$.
Repeated ages and repeated targets are not replaced by representative
indices. An empty support requires no output on a promised source and
is vacuously target-constant, as in NARC Definition 10.1.

The notation $\widehat P_s$ means only the algebraic partition
(NARC.10.5), for an arbitrary integer $s$. It is not a new request.
Actual requests below use only $E$ and $P_t$ with $t\ge2$; there is
no native $P_1$. Their literal suffixes are the supplied
$w_0=\varepsilon$, $w_{2m}=R^m$ and $w_{2m+1}=LR^m$ for $m\ge1$.
At a right-visible entry the whole original-root request is $Lw_t$;
at a left-visible entry it is $Rw_t$. Every letter is materialized,
and $E$ therefore submits the paid word $L$ or $R$, not the
uninformative original-root empty word.

**Lemma 1.2 (nonnegative translation with a common zero/one target).**
Suppose the reference state of Definition 1.1 has a native target
tree of depth at most $k$. If both ages zero and one occur in its
translated restriction, suppose every index at either of these two
ages has one common target. Then the entire translated restriction
has an actual native target tree of depth at most $k$. The result
allows arbitrary finite supports and arbitrary repeated target values,
and applies after every adaptive support restriction.

**Proof.** Refine each reference $S_t$ to $P_t$ with the supplied
reply map of NARC Definition 5.3, and delete reference $E$ and other
constant-reply nodes, as in NARC Theorem 10.2. Reference ages are at least
two, including on descendants, so $E$ is constant branch there.
This leaves a finite reference tree using only $P_t$, $t\ge2$,
with no greater depth. Reference correctness also excludes unequal
targets at equal reference ages: those indices have identical replies
at every native request and hence the same terminal target.
Translation preserves equality of ages and keeps all indices.

Maintain a reference node and the complete translated support surviving
the preceding actual replies. At its threshold $t$, put $s=t+\Delta$.
For each retained index, $\widehat P_s(n_i)=P_t(N_i)$.
The following replacements act on nonnegative actual ages:

| Shifted threshold $s$ | Actual request | Reference child selected by the actual reply |
| --- | --- | --- |
| $s\ge2$ | $P_s$ | The child of that same reply |
| $s=0$ | $E$ | The child of that same reply |
| $s=-1$ | $E$ | $\alpha\mapsto\beta$; $\beta,\mathsf b\mapsto\mathsf b$ |
| $s\le-2$ | None | Follow the reference $\mathsf b$ child locally |
| $s=1$ | $P_2$ | $\alpha\mapsto\beta$; $\beta,\mathsf b\mapsto\mathsf b$; handle $\bot$ as below |

For $s=1$, the actual absence support contains exactly the surviving
indices at ages zero or one. If only age zero occurs, follow the
reference $\bot$ child; if only age one occurs, follow its $\alpha$
child. If both occur, halt this entire absence support at their common
target. If neither occurs, absence is impossible on the promised
support. These cases are selected from the public indexed support,
not by observing an unacquired hidden age. All other actual reply
supports retain every index giving that reply.

To verify the replacements, $s=0$ gives exactly the $E$ law. At
$s=-1$, age zero needs the algebraic reply $\beta$, and every
positive age needs $\mathsf b$. At $s\le-2$ every nonnegative age
needs $\mathsf b$. At $s=1$, actual $P_2$ returns $\alpha$ only
at age two, which needs algebraic $\beta$; its $\beta$ and
$\mathsf b$ cells have ages at least three, which need algebraic
$\mathsf b$. Its absence cell has the cases just described.
Thus each nonhalting actual child has support contained in the
corresponding reference child. The sole child that can merge two
reference replies halts correctly on its whole support.

The common-target condition at ages zero and one is hereditary under
restriction: if both survive, they retain the original common target.
Induction on the remaining height of the finite reference tree now
proves correctness on every surviving index, including adaptive
descendants. A local skip strictly descends that tree; each paid
replacement consumes at most one call in place of one reference call.
Hence all local descents terminate and every actual path uses at most
$k$ calls. A reference leaf is still target-constant on any restriction.
This also proves the empty-support and $k=0$ cases. The replacements
are realized by the actual words of Definition 1.1. $\square$

**Theorem 1.3 (complete-boundary absorber and exact adjacent-repeat locus).**
For any encoder $e$ in NARC Assumption 9.1 define the public set

$$
\mathcal J(e)=\{z\in\mathbb Z:1\le z<q,\ e(0,z)=e(0,z-1)\}.
\tag{NARZ.1.1}
$$

For every finite budget $k\ge0$, both-cut recovery at every
nonnegative lag with at most $k$ chronological native Reads is
equivalent to $D_k$ on both full reference states of every attained
class and on the complete states $S_0(z)$ of (NARC.10.4) for
$z\in\mathcal J(e)$ only. Each retained $S_0(z)$ contains every
$(a,b)\in C_{e(0,z)}$ with $b\le z$, including all its positive-age
alternatives.

Under the full reference certificates, $\mathcal J(e)$ is exactly
the locus where a complete zero-containing boundary state has an
age-one target different from its age-zero target. Thus absence of
adjacent repeated labels in row zero suffices to extend positive-lag
service to nonnegative-lag service at the same budget. It is not a
necessary condition: an adjacent repeat may have a successful complete
boundary certificate. The equivalence does not assert failure or
logical independence of the retained tests.

**Proof.** Necessity follows from NARC Theorem 10.2 by retaining fewer
of its necessary boundary tests. For sufficiency assume the stated
reference and retained boundary certificates. Full reference
readability forces $d=a-b$ to be injective in each class, by the
supplied collision obstruction in NARC Theorem 9.2. Equivalently, equal
right-reference ages must have equal $b$ targets, and equal $d$ and
$b$ then fix $a$.

Fix $0\le z<q$ and retain the entire $S_0(z)$, with ages
$n=z+a-b=a+(z-b)$ and targets $b$. Since $a\ge0$ and $b\le z$,
an age-zero origin is uniquely $(0,z)$, with target $z$. An age-one
origin can only be $(0,z-1)$, at lag one and target $z-1$, or
$(1,z)$, at lag zero and target $z$, when these pairs are in the
square and class. The two possible age-one origins have the same
difference $1-z$, so injectivity permits at most one of them in that
class. For $z\ge1$, the differing-target origin $(0,z-1)$ belongs
to this boundary class exactly when $e(0,z-1)=e(0,z)$, which is
exactly $z\in\mathcal J(e)$. Otherwise an age-one origin, if
present, has the same target as age zero. This proves the exact
locus assertion, including same-target zero/one occurrences.

For $z\notin\mathcal J(e)$ and $z\ge1$, take the right full
reference witness for $C_{e(0,z)}$, restrict it to every member with
$b\le z$, and translate by $\Delta=z-Z$. Its reference ages are
$Z+a-b\ge2$, and its translated indexed state is exactly $S_0(z)$.
Lemma 1.2 supplies a depth-at-most-$k$ actual tree, keeping every
origin in that complete fiber. The reference witness uses
$\mathcal M_q$. Since $z<q$ and $Z=q+1$, $\Delta<0$, so every
replacement $P_s$ with $s\ge2$ still has $s\le3q+1$; the other
paid replacements are $E$ or $P_2$. The resulting tree therefore
supplies $D_k$ in precisely the finite menu of NARC Definition 10.1.
At $z=0$ all retained origins have $b=0$, so $D_0$ already holds.
Every omitted boundary test has now been supplied.

Together with the assumed complete certificates at
$\mathcal J(e)$, these are all the boundary tests of NARC Theorem 10.2.
That theorem yields every nonnegative lag and both cuts. In detail,
all left-hidden ages are positive, and a right entry has an age-zero
candidate only at the recognizable input
$(e(0,z),\mathcal R^R_z)$ with $z<q$. Its positive-support translation
serves every other entry. Initialization always uses the full fiber
of NARC Theorem 5.2; each actual reply keeps every compatible origin, and
the actual original survives. A terminal common target $v$ gives
its own lag $z-v$. Nothing selects a hidden original from a
target-constant leaf or consults the discarded row.

For nonnecessity, reuse the published encoder $e_{17}$ of NARC Definition
11.1: (NARC.11.7) gives $e_{17}(0,10)=e_{17}(0,11)=6$, whereas
NARC Theorem 11.5 certifies all its complete zero fibers with budget two.
Their lawful schedules are already supplied there. A repeat alone
therefore implies neither failure nor the need for an extra call.
When $q=1$, $\mathcal J(e)$ is empty and every target is zero,
so the equivalence includes zero-call service. For arbitrary $q$,
the proof uses only target constancy at budget zero and the same
finite-tree induction at higher budgets. Empty reply supports are
vacuous throughout. $\square$

The mathematical suppliers of Theorem 1.3 are NARC Theorems 5.2, 9.2
and 10.2 and the native menu of NARC Definition 5.3. The two-read
equality, defect, saturated-boundary and packing results of NARC §§13--16
remain their own results; no shape restriction from them is needed
for Lemma 1.2. The incremental statements here are the common-target
translation and its exact row-zero locus for arbitrary finite budgets.
They are `repo-derived` ordinary deductions under these suppliers.
The literature-attested target-conflict ingredient is Charpenay,
Le Treust and Roumy, [*Optimal Zero-Error Coding for Computing under
Pairwise Shared Side Information*, arXiv:2211.03649v2, Definitions
II.1 and III.1](https://arxiv.org/html/2211.03649v2): different required
outputs at a common compatible side-information value must be
separated. The permitted-query distinction is Nowak, [*The Geometry
of Generalized Binary Search*, arXiv:0910.4397v5, §§I--II and
V.A](https://arxiv.org/html/0910.4397v5). Their probabilistic
prefix-code rate and binary hypothesis-identification bounds,
respectively, do not supply the native missing-$P_1$ replacement or
the adjacent-repeat equivalence. This bounded correspondence makes
no global priority claim.

Every actual $E$ costs one chronological call at the hidden-slot
word, and every actual $P_t$ costs one at a whole word of length
$1+\lceil t/2\rceil$. These are the same payment and address
conventions as NARC Definition 12.3. Lemma 1.2 preserves the call upper
bound; it asserts no equality of submitted lengths or of other
resource coordinates before and after translation. Acquiring and
storing whole rows, parsing, retained-label and public-table
representation, local arithmetic, changing workspace, address
production, total submitted length, output size and physical time
remain separate costs. Runtime thresholds at unbounded lags remain
input-dependent. No uniform address bound, fixed finite Moore
implementation, physical service or kernel verification follows.
The unrestricted $q=18$ and $q=19$ cover questions under both lag
conventions remain the unresolved questions of NARC Definition 16.3;
absorbing a redundant boundary test constructs neither cover.

## 追加锚（本行以下为增补区）

## 2. The same acquired code supports two task controllers

**Definition 2.1 (unchanged export and the joint output).** Retain exactly
NARC Assumptions 5.1 and 9.1 and the specialization of
[NAR Assumption 16.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md)
to two slots. Fix public $1\le q\le17$. The encoder is precisely
$e_q$ of NARC Definition 11.1, computed from the genuinely acquired
initial empty-cut row, with exactly its $q$ attained labels. It exports
this label before the future cut and lag and discards all other
source-bearing fields. No task choice changes the export. The task
may be selected after that export; it selects one of two controllers
from public data, without retaining a source-dependent controller state.

The lag controller returns $\ell$. The joint controller returns the
ordered triple $(a,b,\ell)$, identifying the entire mathematical
original $X_{a,b}=\langle T_a,T_{q+b}\rangle$ as well as the lag.
If a literal original is requested as output, construct this finite
literal from the recovered coordinates and the defining recurrence
for $T_n$; its construction and output are separately charged. Neither
output identifies physical occurrence names, an actual history archive,
ownership or rights, nor performs a physical Return of an earlier source.

For singleton cuts use the entire acquired fibers from NARC Theorem 5.2.
It is convenient to orient each candidate as follows:

$$
\begin{array}{c|cccc}
\text{visible slot}&u&v&h&\text{hidden-slot prefix }p\cr\hline
R&a-b&b&z&L\cr
L&b-a&a&q+z&R
\end{array}
\qquad n=h+u,\qquad \ell=z-v.
\tag{NARZ.2.1}
$$

Here $z$ is parsed solely from the genuinely acquired visible literal:
$z=c(T_{q+b+\ell})-q$ or $z=c(T_{a+\ell})$, respectively.
At initialization retain every candidate of the received class with
$v\le z-\lambda$, where $\lambda\in\{0,1\}$ is the public lag
convention. Each candidate retains its original ordered pair $(a,b)$.
After a reply retain exactly every candidate producing that actual
reply. A joint terminal support must be a singleton original, even
when all its candidates would give the same lag.

By NARC Proposition 11.2, $a-b$ is injective in each class; hence so
is either oriented $u$. Symmetry of the same encoder allows one
oriented certificate table for both cuts. This uses the original
offsets $0,q$ in (NARZ.2.1), including every smaller prefix $q$.
No seventeen-offset source is substituted for a smaller-$q$ source.

**Definition 2.2 (finite singleton certificates).** For an integer $s$,
write $Q(s)$ for the inherited partition of an oriented coordinate $u$
into $u<s$, $u=s$, $u=s+1$, $u\ge s+2$, in reply order
$(\bot,\alpha,\beta,\mathsf b)$. This is partition notation,
not an extra experiment. At reference age $N=18+u$ it is the actual
$P_{18+s}$ whenever $18+s\ge2$.

The following notation specifies complete depth-at-most-three trees.
A row gives a first threshold and second thresholds after first
absence and first branch. The two middle replies always have at most
one original, by injectivity. A dot means that the corresponding
support has size at most one and halts without a request. The last
four columns give the complete nonsingleton supports after the two
tail replies, together with their final separating threshold. An entry
$S\to s$ means query $Q(s)$ on exactly that support $S$; all its
resulting cells have size at most one. The double-tail columns are
ordered $\bot\bot,\bot\mathsf b,\mathsf b\bot,
\mathsf b\mathsf b$. Any omitted support in those columns has size
at most one. Empty cells are impossible on a promised source and
require no output. Singleton halting and constant-reply pruning may
also be performed earlier by inspecting the public surviving support.
All intervals in the tables are inclusive integer intervals.

**Lemma 2.3 (complete positive-class singleton certificates).** Each
master class of $e_{17}$ has the following full oriented difference
support $U_c$. These are the class geometry of NARC Proposition 11.2,
used here without a new encoder or class-bound claim; $\pm S$ means
$S\cup(-S)$.

| $c$ | Complete $U_c$ | Size |
| --- | --- | --- |
| $0$ | $\{0\}\cup\pm[10,16]$ | $15$ |
| $1$ | $[-1,1]\cup\pm[10,15]$ | $15$ |
| $2$ | $[-2,2]\cup\pm\{10,13,14\}$ | $11$ |
| $3$ | $[-3,3]\cup\pm[10,12]$ | $13$ |
| $4$ | $[-4,4]\cup\pm[10,12]$ | $15$ |
| $5$ | $[-5,5]\cup\pm[10,12]$ | $17$ |
| $6$ | $[-6,6]\cup\pm\{10,11,13\}$ | $19$ |
| $7$ | $[-7,7]$ | $15$ |
| $8$ | $[-8,8]$ | $17$ |
| $9\le c\le16$ | $[-9,9]$ | $19$ |

On these entire supports the following trees terminate at singleton
originals within three reference Reads:

| $c$ | First | Second $\bot$ | Second $\mathsf b$ | $\bot\bot$ | $\bot\mathsf b$ | $\mathsf b\bot$ | $\mathsf b\mathsf b$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $0$ | $-12$ | $-16$ | $11$ | $\cdot$ | $\{-14,-13\}\to-15$ | $\{-10,0,10\}\to-1$ | $[13,16]\to14$ |
| $1$ | $-12$ | $-16$ | $10$ | $\cdot$ | $\{-14,-13\}\to-15$ | $[-1,1]\cup\{-10\}\to-1$ | $[12,15]\to13$ |
| $2$ | $-14$ | $\cdot$ | $1$ | $\cdot$ | $\cdot$ | $[-2,0]\cup\{-10\}\to-2$ | $\{10,13,14\}\to12$ |
| $3$ | $-11$ | $\cdot$ | $1$ | $\cdot$ | $\cdot$ | $[-3,0]\to-2$ | $\{3,10,11,12\}\to10$ |
| $4$ | $-4$ | $-13$ | $2$ | $\cdot$ | $\{-11,-10\}\to-12$ | $[-2,1]\to-1$ | $\{4,10,11,12\}\to10$ |
| $5$ | $-3$ | $-12$ | $3$ | $\cdot$ | $\{-10,-5,-4\}\to-6$ | $[-1,2]\to0$ | $\{5,10,11,12\}\to10$ |
| $6$ | $-2$ | $-11$ | $4$ | $\cdot$ | $[-6,-3]\to-5$ | $[0,3]\to1$ | $\{6,10,11,13\}\to10$ |
| $7$ | $-4$ | $-8$ | $2$ | $\cdot$ | $\{-6,-5\}\to-7$ | $[-2,1]\to-1$ | $[4,7]\to5$ |
| $8$ | $-3$ | $-9$ | $3$ | $\cdot$ | $[-7,-4]\to-6$ | $[-1,2]\to0$ | $[5,8]\to6$ |
| $9\le c\le16$ | $-2$ | $-8$ | $4$ | $\cdot$ | $[-6,-3]\to-5$ | $[0,3]\to1$ | $[6,9]\to7$ |

**Proof.** Intersect each listed $U_c$ with the four cells of its
first partition, then intersect its two tail cells with the indicated
second partitions. Their middle cells are singleton coordinates.
The last four columns list every remaining nonsingleton cell, with
all its members, so no target-constant multi-original leaf is suppressed.
For example, class zero's first lower cell is $[-16,-13]$.
Its second threshold $-16$ singles out $-16,-15$ and leaves
$\{-14,-13\}$ in branch. Its first upper cell is
$\{-10,0\}\cup[10,16]$; threshold eleven leaves
$\{-10,0,10\}$ and $[13,16]$ as its tails. These are exactly
the four-column entries for that class, including its empty double
absence. The same intersections give every row displayed above.

For each final entry $S\to s$, direct comparison gives
$|S\cap(-\infty,s)|\le1$ and
$|S\cap[s+2,\infty)|\le1$. Its middle cells $\{s\}$ and
$\{s+1\}$ also have size at most one. This verifies every final
partition, including gapped sets such as $\{6,10,11,13\}\to10$:
its four cells are $\{6\},\{10\},\{11\},\{13\}$.
Thus every nonempty terminal cell has one coordinate and hence one
original. The least offset used is $-16$, so at $N=18+u$ all
requests are actual $P_t$ with $t\ge2$. All these reference ages
are at least two. Prefix and entry restrictions only delete original
indices and preserve the singleton property. $\square$

**Lemma 2.4 (complete zero-containing singleton certificates).** Put
$c_z=e_{17}(0,z)$ and define the complete master boundary support

$$
B_z=\{(a,b):e_{17}(a,b)=c_z,\ 0\le a,b\le16,\ b\le z\},
\qquad A_z=\{z+a-b:(a,b)\in B_z\},\quad 0\le z\le16.
\tag{NARZ.2.2}
$$

Its ages are distinct by the inherited difference injectivity. The
following are the entire age sets, including every positive-age
alternative to the zero-age original:

| $z$ | $c_z$ | Complete $A_z$ | Size |
| --- | --- | --- | --- |
| $0$ | $0$ | $\{0,16\}$ | $2$ |
| $1$ | $1$ | $[0,2]\cup\{15,16\}$ | $5$ |
| $2$ | $2$ | $[0,4]\cup\{15,16\}$ | $7$ |
| $3$ | $3$ | $[0,6]\cup\{14,15\}$ | $9$ |
| $4$ | $4$ | $[0,8]\cup[14,16]$ | $12$ |
| $5$ | $5$ | $[0,10]\cup[15,17]$ | $14$ |
| $6$ | $6$ | $[0,12]\cup\{16,17,19\}$ | $16$ |
| $7$ | $7$ | $[0,14]$ | $15$ |
| $8$ | $8$ | $[0,16]$ | $17$ |
| $9$ | $9$ | $[0,18]$ | $19$ |
| $10$ | $6$ | $\{0\}\cup[4,16]\cup\{20,21,23\}$ | $17$ |
| $11$ | $6$ | $\{0,1\}\cup[5,17]\cup\{21,22,24\}$ | $18$ |
| $12$ | $3$ | $\{0\}\cup[9,15]\cup[22,24]$ | $11$ |
| $13$ | $6$ | $\{0,2,3\}\cup[7,19]\cup\{23,24,26\}$ | $19$ |
| $14$ | $2$ | $\{0,1,4\}\cup[12,16]\cup\{24,27,28\}$ | $11$ |
| $15$ | $1$ | $[0,5]\cup[14,16]\cup[25,30]$ | $15$ |
| $16$ | $0$ | $[0,6]\cup\{16\}\cup[26,32]$ | $15$ |

Use the same complete-tree convention as Definition 2.2, now on the
actual age $n$. A threshold zero means actual $E$, with no absent
cell, singleton alpha/beta cells, and branch cell $n\ge2$.
Every other threshold displayed is at least two and means actual
$P_t$. In particular, none means $P_1$.

| $z$ | First | Second $\bot$ | Second $\mathsf b$ | $\bot\bot$ | $\bot\mathsf b$ | $\mathsf b\bot$ | $\mathsf b\mathsf b$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $0$ | $0$ | $\cdot$ | $\cdot$ | $\cdot$ | $\cdot$ | $\cdot$ | $\cdot$ |
| $1$ | $0$ | $\cdot$ | $2$ | $\cdot$ | $\cdot$ | $\cdot$ | $\{15,16\}\to14$ |
| $2$ | $0$ | $\cdot$ | $2$ | $\cdot$ | $\cdot$ | $\cdot$ | $\{4,15,16\}\to14$ |
| $3$ | $0$ | $\cdot$ | $4$ | $\cdot$ | $\cdot$ | $\{2,3\}\to2$ | $\{6,14,15\}\to13$ |
| $4$ | $0$ | $\cdot$ | $6$ | $\cdot$ | $\cdot$ | $[2,5]\to3$ | $\{8,14,15,16\}\to14$ |
| $5$ | $2$ | $0$ | $8$ | $\cdot$ | $\cdot$ | $[4,7]\to5$ | $\{10,15,16,17\}\to15$ |
| $6$ | $4$ | $0$ | $10$ | $\cdot$ | $\{2,3\}\to2$ | $[6,9]\to7$ | $\{12,16,17,19\}\to16$ |
| $7$ | $3$ | $0$ | $9$ | $\cdot$ | $\cdot$ | $[5,8]\to6$ | $[11,14]\to12$ |
| $8$ | $5$ | $0$ | $11$ | $\cdot$ | $[2,4]\to2$ | $[7,10]\to8$ | $[13,16]\to14$ |
| $9$ | $7$ | $2$ | $13$ | $\{0,1\}\to0$ | $[4,6]\to4$ | $[9,12]\to10$ | $[15,18]\to16$ |
| $10$ | $8$ | $0$ | $14$ | $\cdot$ | $[4,7]\to5$ | $[10,13]\to11$ | $\{16,20,21,23\}\to20$ |
| $11$ | $9$ | $0$ | $15$ | $\cdot$ | $[5,8]\to6$ | $[11,14]\to12$ | $\{17,21,22,24\}\to21$ |
| $12$ | $0$ | $\cdot$ | $13$ | $\cdot$ | $\cdot$ | $[9,12]\to10$ | $\{15,22,23,24\}\to22$ |
| $13$ | $11$ | $2$ | $17$ | $\cdot$ | $[7,10]\to8$ | $[13,16]\to14$ | $\{19,23,24,26\}\to23$ |
| $14$ | $0$ | $\cdot$ | $15$ | $\cdot$ | $\cdot$ | $\{4,12,13,14\}\to12$ | $\{24,27,28\}\to26$ |
| $15$ | $3$ | $0$ | $25$ | $\cdot$ | $\cdot$ | $\{5,14,15,16\}\to14$ | $[27,30]\to28$ |
| $16$ | $4$ | $0$ | $27$ | $\cdot$ | $\{2,3\}\to2$ | $\{6,16,26\}\to15$ | $[29,32]\to30$ |

These trees identify the original in every $B_z$ within three Reads.
For every prefix $q$ and $z<q$, restriction to $a,b<q$ gives the
entire corresponding zero-containing fiber with its same actual ages.

**Proof.** Obtain $B_z$ by retaining every pair of its encoder class
with $b\le z$, then substitute $n=z+a-b$. The base arms and extras
in NARC Proposition 11.2 give exactly the displayed $A_z$. For
example, at $z=11$ class six has feasible negative extras of ages
zero and one, its base gives $[5,17]$, and its positive extras give
$21,22,24$. At $z=0$ the complete class-zero fiber contains both
$(0,0)$ and $(16,0)$, with ages zero and sixteen. A zero lag target
does not permit merging these originals.

Intersect each displayed $A_z$ with its first and second actual reply
cells. As in Lemma 2.3, singleton middle cells terminate, and the last
four columns enumerate every remaining nonsingleton cell. Every
listed final $S\to t$ has at most one age below $t$ and at most
one age above $t+1$, with singleton middle cells. For $t=0$, the
only such final support is $\{0,1\}$ and actual $E$ separates it.
The other zero thresholds occur in the first two levels, using the
stated actual $E$ law on their whole supports. Thus every terminal
nonempty cell has one age and, by injectivity, one original.

If $z<q$, restriction of the master encoder satisfies
$e_q(0,z)=c_z$, and its complete compatible boundary fiber is
$B_z\cap[0,q-1]^2$. The formula $n=z+a-b$ for its hidden left
slot is independent of the right offset $q$. The acquired exterior
remains the actual $T_{q+z}$. Restricting these certificates therefore
changes no native request meaning and omits no prefix alternative.
This proves every complete boundary claim, including the two adjacent
row-zero labels at clocks ten and eleven. $\square$

**Theorem 2.5 (same-code lag and joint recovery at all nonnegative lags).**
For every public $1\le q\le17$, the unchanged acquired encoder
$e_q$ admits two separate task controllers under Definition 2.1:

- a lag controller using at most two fresh chronological native Reads;
- a joint controller using at most three such Reads and returning the
  entire original pair $(a,b)$ and $\ell$.

Both work on either singleton cut, for every original in the square
and every integer $\ell\ge0$. The same statements hold with public
positive-lag convention $\ell\ge1$. Task selection may follow the
initial export. These are alternative services of the same code;
the joint controller need not extend the lag controller's transcript.

If the later cut is empty and the complete later empty-cut row is
already genuinely acquired under NAR Assumption 16.1, the same code
returns $(a,b,\ell)$ with zero fresh Reads. This zero-fresh-Read
statement includes reconstruction of the mathematical original literal
when its separately charged construction/output is requested; it does
not price the full current-row acquisition as zero.

**Proof, lag service.** Reuse NARC Theorem 11.6 with its same $e_q$,
not a newly encoded initial coordinate. Its complete certificates and
all-lag translation supply the two-Read service. Neither the new
joint task nor its controller changes any input to that theorem.

**Proof, branch selection for the joint service.** Initialize the exact
finite candidate set in (NARZ.2.1). The actual original survives and
has its own legal continuation; all competing indices are the complete
same-entry histories of NARC Theorem 5.2. On a right-visible entry a
candidate age $n=z+a-b=a+\ell$ can be zero only for
$a=0$, $\ell=0$, $b=z$. Thus a zero-containing entry exists
exactly when $\lambda=0$, $0\le z<q$ and
$\gamma=e_q(0,z)$. Every part of this test is public or acquired.
On such an entry use the corresponding complete tree of Lemma 2.4,
restricted to the actual prefix square. Do not run a positive-support
tree just on its zero-age member. The entire fiber, with all its
positive-age alternatives, follows the certified boundary tree.
All other right entries have positive hidden support, and every left
entry has $n=q+b+\ell\ge q\ge1$.

**Proof, source-faithful translation on every positive support.** Choose
the class tree of Lemma 2.3 and restrict it to the exact candidate
indices. Its algebraic reference ages are $N_i=18+u_i\ge2$.
At the current entry their actual ages are $n_i=h+u_i$, so the
common shift is $\Delta=h-18$. The reference objects only specify
a finite public certificate; they neither supply an acquired hidden
age nor invoke a reference source. A reference threshold $18+s$
translates to $t=h+s$. On the current positive support implement
its algebraic reply as follows:

| $t$ | Actual relative request | Reply passed to the reference node |
| --- | --- | --- |
| $t\ge2$ | $P_t$ | Same reply |
| $t=1$ | $P_2$ | $\bot\mapsto\alpha$, $\alpha\mapsto\beta$, $\beta,\mathsf b\mapsto\mathsf b$ |
| $t=0$ | $E$ | Same reply |
| $t\le-1$ | No request | Constant $\mathsf b$ |

For $t=1$, positive actual absence under $P_2$ means exactly
$n=1$, which is the algebraic alpha cell; actual alpha means
$n=2$, which is its beta cell. Both higher actual replies belong
to its branch cell. For $t=0$ actual $E$ has exactly the algebraic
partition on positive ages; for $t\le-1$ every positive age is
at least $t+2$. For $t\ge2$ the identity is the native law.
Consequently, every surviving origin follows its own reference path
under the indicated reply maps. Keep the complete support of each
actual reply, even when two actual replies map to one reference child.
All arithmetic and child choices use acquired $h$, the public class
and previous actual replies. No hidden original is selected locally.

Realize every paid request at the same stationary CURRENT original
root: submit $p$ for $E$, or $p w_t$ for $P_t$, with
$p$ from (NARZ.2.1) and
$w_{2m}=R^m$, $w_{2m+1}=LR^m$ for $m\ge1$.
In the threshold-one replacement use $pR$, namely actual $P_2$.
Each word is fully materialized; in particular, $E$ is the paid
hidden-slot word rather than a free root observation. No $P_1$,
subtree query, unacquired age, old-source reread or new port is used.
The positive reply maps are the source-law identities in NARC
Theorem 10.2, applied here with singleton-original terminal targets.

A local skip or a constant-reply pruning step strictly descends a
finite tree. Each non-skipped node uses at most one paid request.
The remaining height starts at at most three, so every local path
terminates and every execution uses at most three fresh Reads.
The boundary trees have the same height bound and use only actual
$E/P_t$ requests. Initial parsing and each finite enumeration also
terminate on finite acquired rows and tables. The actual original
survives every actual reply restriction. Every nonempty terminal
support is a singleton $(a,b)$ by Lemmas 2.3--2.4, so returning
$\ell=z-v$ gives that original's actual lag. This is stronger than
halting at a lag-constant leaf and does not infer an original from
lag alone. The translation identities hold for all positive integers
$n$ and all integer thresholds $t$; no finite lag window is used
to justify the unbounded-lag quantifier.

**Proof, the empty cut.** Parse both ages $n_L=a+\ell$ and
$n_R=q+b+\ell$ from the already acquired entire current literal.
Their normalized difference is
$d=n_L-(n_R-q)=a-b$. Enumerate the received $e_q$ class and retain
pairs with this difference and a common legal
$\ell=n_L-a=n_R-q-b$. The actual pair survives. Difference
injectivity in that class leaves exactly one pair. Thus no new
source call is required to return $(a,b,\ell)$ or to construct its
mathematical original. This argument uses the full acquired empty-cut
row; it cannot be substituted for either singleton-cut entry. $\square$

**Proposition 2.6 (one extra Read after the lag transcript need not suffice).**
The three-Read joint controller in Theorem 2.5 cannot in general be
obtained by appending one Read to the published two-Read lag
transcript of NARC Theorem 11.5.

**Proof.** Use $q=17$, right visibility, label zero and $z=17$.
For each of the seven originals $(a,b)=(a,16)$, $0\le a\le6$,
take its own lag $\ell=1$. These are all allowed originals of that
same code, with the same entire acquired exterior $T_{34}$ and the
same singleton reached left hole. Their hidden ages are $1,\ldots,7$.
The published class-zero lag tree requests $P_{28}$ and, after
absence, $P_{17}$ in that slot, namely the whole words $LR^{14}$
and $LLR^8$. All seven give $(\bot,\bot)$ and correctly halt
with lag one. The lower negative-extra block in the complete
class-zero fiber is exactly these seven surviving originals.

Any next whole-root word is selected from their common entry and
transcript. It has at most the four actual constructor/absence
replies, so cannot separate seven required original outputs. Root
and visible-prefixed words are constant on the same entry as well.
Thus no single further Read and local computation can finish joint
recovery on that lag transcript. This refutes the transcript-extension
claim while preserving both separate services of Theorem 2.5. $\square$

**Corollary 2.7 (simultaneously optimal supported call pair).** For
$11\le q\le17$ and either lag convention, the same $e_q$ supports
worst-call pair $(2,3)$ for the lag and joint tasks respectively,
and each coordinate is optimal among all exactly-$q$-label encoders
under this same source/current-Read contract. The word
“simultaneously” concerns two alternative task controllers following
one unchanged export, not a shared two-Read prefix.

**Proof.** The upper bounds are Theorem 2.5. For the lag task reuse
exactly NARC Theorems 7.5 and 12.1, which exclude one Read for
$q\ge7$ under either convention. For entire-original recovery reuse
exactly NARC Proposition 12.2: any such service with $k$ Reads and
exactly $q$ attained labels necessarily has
$q\le3\cdot2^k-2$. At $k=2$ this excludes $q\ge11$.
Joint recovery includes its original-recovery target, so this lower
bound applies unchanged. These existing bounds prove each coordinate
sharp; no new lower-bound argument is asserted here. $\square$

## 3. Same-code correspondence and the preserved resource boundary

The increment of Lemmas 2.3--2.4 and Theorem 2.5 is `repo-derived`:
singleton-original certificates for the SAME prior $e_q$ coexist with
its supplied two-Read lag service. NARC Definition 11.1 supplies the
encoder; Proposition 11.2 supplies its attained alphabet, symmetry,
class geometry and difference injectivity; Theorem 5.2 supplies the
complete acquired fibers and same-original histories; Definition 5.3
supplies every permitted literal response law; Theorem 10.2 supplies
the positive query-translation identities; Theorem 11.6 supplies the
lag controller. The lower bounds in Corollary 2.7 remain precisely
the reused results cited there. Section 1, including its arbitrary-budget
lag absorber, addresses coordinate targets and is not substituted for
the singleton-original boundary certificates above.

Standalone original recovery with three Reads is already available
for $q\le17$ with the different fixed code $e(a,b)=b$. For right
visibility this code fixes $\ell=z-b$ and leaves at most $q$
consecutive hidden left ages; for left visibility it leaves at most
$q$ consecutive hidden right ages, whose identification determines
$a$ and $\ell$. Reuse the actual interval readers of
[Acquired orbit resource frontier, Theorem 8.3](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md):
their three-Read capacities are $22$ on positive intervals and $21$
on intervals starting at zero. They cover both cases here. NARC
Theorem 12.1 already shows that this fixed-$b$ code needs three
Reads for lag when $11\le q\le17$. Thus the new point is keeping
the two-Read lag service while supporting three-Read original recovery
with its SAME exported $e_q$, rather than asserting a new standalone
three-Read capability or a new general inversion principle.

The mature search ingredient is restricted-query hypothesis
identification: a controller recursively partitions its compatible
hypotheses by permitted actual replies until the requested output is
constant. For the joint task each output is a distinct original.
Nowak, [*The Geometry of Generalized Binary Search*,
arXiv:0910.4397v5, §§I--II and V.A](https://arxiv.org/html/0910.4397v5),
studies hypothesis identification by selected binary queries and
explains the dependence on the allowed query space. That correspondence
supplies neither arbitrary native subset tests nor a numerical call
bound here: the four native cells, missing $P_1$, and the complete
zero-containing trees require the explicit certificates above.

The mature output-conflict ingredient is zero-error computation with
side information: two source alternatives giving the same side
information but different required outputs must be distinguished.
Charpenay, Le Treust and Roumy,
[*Optimal Zero-Error Coding for Computing under Pairwise Shared Side
Information*, arXiv:2211.03649v2, Definitions II.1 and
III.1](https://arxiv.org/html/2211.03649v2), provide that correspondence
through characteristic graphs. Their probabilistic prefix-code rates
and asymptotic graph-entropy objectives do not give the actual native
three-Read singleton trees or simultaneous same-code pair. These
correspondences distinguish reused search principles from this
source-specific composition and make no historical-priority claim.

Only the maximum fresh chronological Read count is newly bounded.
Every $E$ submission costs one call. A submitted $P_t$ word has
$1+\lceil t/2\rceil$ actual letters including its hidden-slot prefix.
All reference offsets in Lemma 2.3 are at most fourteen, and every
boundary threshold in Lemma 2.4 is at most $z+14$. The positive
translation uses either $P_{h+s}$, actual $P_2$, actual $E$, or a
local skip. Consequently every word of the specified joint controller
has finite length at most $1+\lceil(h+14)/2\rceil$ at its input.
This bound depends on the acquired clock.

For each fixed $2\le q\le17$, that controller's submitted lengths
are unbounded over legal lags. Take right visibility and label one
at arbitrarily large $z$, so the entire class is feasible. If $q<16$,
its restricted class is the maximum-one base; pruning constant nodes
in the class-one tree leaves its required $Q(-1)$, hence actual
$P_{z-1}$. If $q\ge16$, its full star extras are present and the
first $Q(-12)$ is nonconstant, hence actual $P_{z-12}$. These
submitted word lengths diverge. At $q=1$ the sole original is public
and its acquired visible clock already gives the lag with no fresh
Read. A bounded number of calls therefore supplies no uniform
address-length, elapsed-time or finite-installed-memory bound.

Initial acquisition, every later acquisition, all actual $\rho$ work,
full rows and their backing representations, retained-label encoding,
public tables, local parsing/enumeration/arithmetic, certificate
construction, controller construction, changing workspace, materializing
words, total submitted length, discard, any premise authentication,
output construction and output size retain their separate costs. Public finite tables are common to
all sources and contain no retained source selection. The proof assumes
the declared permissions, truthful acquisition/export/discard,
same-original continuation and stationary reading. Its output does
not authenticate any of these premises, infer physical history or
rights, or create a physical Return service. No new acquisition port,
reader installation or uncharged source-bearing state is supplied.

The finite tables and their ordinary proofs are mathematical
certificates, not Lean verification or machine-maintained status
receipts. They address only this native source and its specified
current Read contract. They establish no cross-source identification,
no $q=18$ or $q=19$ cover result, no diffusion or AURIC recovery,
and no completion of the persistent mutual-recovery goal. In
particular, actual S-to-C label assimilation remains outside these
claims.

## 追加锚（本行以下为增补区）
