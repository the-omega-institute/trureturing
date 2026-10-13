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
