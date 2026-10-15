# Native prescribed-code acquisition on the original one-image fiber

This companion to [Native cut-birth provenance and literal past-row
recovery, §§9–15][NBP] separates compatibility of a prescribed reader
code from generation of that same code by paid common-start preparation.
It gives a finite-observation criterion, a sharp context-indexed
preparation frontier, and a compatible acquired-term code that no finite
installed preparer generates on the entire original fiber.

This is an append-only `generic-v1` reference volume. Corrections and
extensions belong after its final append anchor, preserving existing
text. The proofs are ordinary paper mathematics, without a current Lean
kernel claim, executable mathematical verification, or worldwide-priority
claim. Mathematical authorship is by the sole Codex CLI author; the
credited suppliers below retain ownership of the reused results.

## 1. The source, complete rows, and the unchanged permissions

**Definition 1.1 (original native objects).** The source algebra is the
free algebra of finite nonempty ordered trees

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{PCA.1}
$$

Write $\mathcal W=\{L,R\}^{*}$, including the empty word. The actual
reply $r_t(v)$ at any $v\in\mathcal W$ is in
$\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
It gives the constructor at a reached node, and absent after traversal
passes a leaf. Every finite address is legal. Brackets, order, leaf
labels and different occurrences of equal subtrees are retained.

For a finite prefix-free cut $P$, the complete row $R_P(t)$ consists of
the exterior obtained by replacing each reached cut subtree by its
occurrence hole, together with the complete equality partition of those
subtrees. Different classes assert disequality. Concrete exterior leaves
give the strict-prefix blocking guards for unreached cut members.
Class names are recomputed from first occurrences after restriction.
These are exactly [NBP, Definitions 1.1–1.2][NBP], including the canonical
row convention; a root-type list alone is not the required output.

**Assumption 1.2 (arbitrary original full fiber).** Fix a public cut $P$
and complete current row $R_*$. In §§2–3 the domain is any fixed nonempty
fiber

$$
\mathcal U=\{u\in\mathcal T:R_P(\rho u)=R_*\},
\qquad t_u=\rho u,\qquad F(u)=R_P(u).
\tag{PCA.2}
$$

It contains every compatible finite origin, without a size or depth
promise. The single update, origin/register binding and current row
acquisition are authenticated supplied premises. The current register
remains that same $t_u$ through preparation, handoff and reading.

Use [NBP, Assumptions 10.6 and 14.1][NBP] for the general acquisition
and access contracts, with Assumption 9.2 as their repeated-partner
specialization. In the acquired-term description,
$A(u)$ is genuinely acquired same-version data: the complete current
tree, or the row and one acquired finite value for each class. A lawful
finite computation on $A(u)$ specifies the code below. In the paid
common-start preparation description, that acquired archive is
inaccessible: preparation starts source-independently and obtains every
source distinction through its own paid actual native replies. The
acquired-term description specifies which function must be generated;
it does not put its arguments into the preparation state.

Pre-cut native permission, acquisition, authentication, actual export,
complete access isolation, lawful reader entry, handoff and stationary
service continuity remain supplied and separately priced. They are not
constructed from a row identity or from existence of a finite table.
There is no update, reset, reroot, copying, equality, image-membership,
inverse, provenance or source-identity port during the two phases.

## 2. Prescribed complete entry and the counted preparation apparatus

**Definition 2.1 (fixed code and fixed reader).** Let
$c(u)=\kappa(A(u))$ have a finite nonempty attained alphabet
$C=c[\mathcal U]$. Fix the original reader
$\mathcal K=Q\sqcup Z$, its fixed-address four-successor running table,
and its fixed whole-row halt outputs. Fix its original initialization

$$
\iota:C\longrightarrow\mathcal K,\qquad
s(u)=\iota(c(u)),\qquad S=\iota[C].
\tag{PCA.3}
$$

The prescribed code is recoverable from the complete initial reader
state on its attained range: a fixed inverse on $S$ recovers $c$.
Equivalently $\iota$ is injective on $C$. This inverse expresses entry
recoverability; it is not an additional running readout or output port.
The reader starts at precisely $s(u)$ and returns the entire $F(u)$ on
every $u\in\mathcal U$. If such a correct reader is not supplied, a
code-generation criterion alone does not establish two-phase recovery.

The reader table and $\iota$ are held fixed throughout. A preparer must
generate the literal entry $s(u)$, thereby generating the same original
code $c(u)$. It may not substitute another encoding with the same target
information. If the prescribed code is already a reader-state code,
$\iota$ is the identity. No code copy or archive is accessible after
entry; all installed running states and whole-row halt states count.

**Definition 2.2 (common-start preparation).** Use the terminal-latch
convention of [NBP, Definition 14.2][NBP]. Its installed alphabet is

$$
\mathcal B=V\sqcup\widehat S,
\qquad \widehat S=\{\widehat s:s\in S\},
\qquad b_0\in\mathcal B.
\tag{PCA.4}
$$

The start $b_0$ is common to the entire fiber. A running state $v\in V$
has one fixed word $a(v)\in\mathcal W$ and four fixed successors
$N(v,z)\in\mathcal B$, $z\in\mathcal A$. Visiting $v$ makes one
actual invocation at $a(v)$ and takes the successor for its actual
reply. There are no silent control transitions. Latch $\widehat s$
holds the literal complete reader-state code $s$, replaces the running
configuration, and makes no native call. The supplied paid handoff
enters exactly $s$ and makes preparation material inaccessible.

Every installed state counts, including unused states. Extra installed
latches, if required, count too; constructions here need just $\widehat
S$. For a terminating run with running visits $v_1,\ldots,v_m$, put

$$
q_P(u)=m,\qquad
\ell_P(u)=\sum_{j=1}^{m}|a(v_j)|,\qquad
H=|\mathcal B|.
\tag{PCA.5}
$$

The uniform call and literal upper budgets are denoted $p$ and $\ell_P$.
Each visit costs a call, including repeats, absence, and the empty
word; an empty word contributes zero letters. These cardinality and
literal coordinates do not price physical table bytes, local work,
elapsed time, energy, or handoff storage. Installed literals and all
four successors are common data, with their separate representation
and installation prices. The only mutable preparation configuration is
the one counted member of $\mathcal B$.

**Lemma 2.3 (finite menu and stationary termination).** A fixed finite
preparer has the finite installed observing menu
$M=\{a(v):v\in V\}$. Sources agreeing on every word of $M$ have
identical state paths from $b_0$. If preparation terminates on every
source, each run has at most $|V|$ invocations and literal cost at most
$\sum_{v\in V}|a(v)|$.

Proof. Equal current states query the same installed word. Equal menu
replies therefore give equal successors, inductively through the entire
path and its latch. For the bounds, reuse [NBP, Proposition 12.5][NBP]:
on a fixed stationary source, revisiting a running state repeats the
same deterministic suffix forever. A terminating run visits each such
state at most once. Summing its nonnegative literal lengths gives the
second bound. This does not declare the union of paths over different
sources acyclic. Shared successors, cycles in that union, unused states
and repeated literal words at different states remain allowed. $\square$

## 3. Exact finite-observation criterion

**Definition 3.1 (observational constancy).** For a finite menu
$M\subseteq\mathcal W$, let

$$
O_M(u)=(r_{t_u}(w))_{w\in M}.
\tag{PCA.6}
$$

A common ordering of $M$ fixes the tuple notation. Say that $M$
determines the prescribed code when

$$
O_M(u)=O_M(u')\ \Longrightarrow\ c(u)=c(u')
\qquad(u,u'\in\mathcal U).
\tag{PCA.7}
$$

By entry recoverability, this is equivalent to the same implication
with $s(u)=s(u')$. It quantifies over the whole original domain, rather
than one representative of each root profile or target fiber.

**Theorem 3.2 (generation of the same prescribed code).** Under
Assumption 1.2 and Definitions 2.1–2.2, the following are equivalent:

1. Some finite installed common-start preparer terminates with exactly
   $\widehat{s(u)}$ on every $u\in\mathcal U$.
2. Some finite native menu determines $c$ in (PCA.7).
3. For some integer $d\ge0$, agreement of all actual replies at words
   of length at most $d$ implies equality of $c$ on $\mathcal U$.

In item 1 it makes no difference whether a uniform call upper bound
was required in advance or merely termination on each source.

Proof. For 1 implies 2 take the installed menu of Lemma 2.3. Its equal
reply tuples force equal terminal latches. Recoverability then forces
equal original codes. This also proves the assertion about termination
without a predeclared bound.

For 2 implies 1, list a determining menu as $w_1,\ldots,w_m$. For
$0\le j\le m$ let $T_j\subseteq\mathcal A^j$ be the set of attained
reply prefixes to these first $j$ words on the entire $\mathcal U$.
Nonemptiness gives $T_0=\{()\}$. Install one running state for each
member of $T_j$, $j<m$, querying the fixed literal $w_{j+1}$. An attained
one-letter extension goes to its next prefix state, or, at level $m$,
to the latch for its prescribed $s$ value. This last value is
well-defined by (PCA.7) and (PCA.3). Each unattained extension is assigned
one fixed existing latch, making the table total on all four replies.
These off-domain choices affect no actual run. If $m=0$, the code is
constant and the common start is its one latch.

Induction on $j$ shows that an actual source reaches exactly its
attained prefix state, and after $m$ calls reaches exactly its original
entry-code latch. The finite prefix labels are the installed running
states themselves. They are not a free transcript register, counter,
selector or address-computation facility. The last transition installs
the literal entry code; handoff uses inclusion into the already fixed
reader alphabet, without an extra decoder. This is a finite mathematical
construction of tables, not an assumed algorithm for discovering
attainability or the values of an arbitrary $\kappa$.

For 2 implies 3, choose $d$ at least the length of every menu word,
with $d=0$ for an empty menu. The larger finite observation implies
agreement on the menu. For 3 implies 2, use the finite menu of all words
of length at most $d$. Both implications use the original native words
and replies on the original domain. $\square$

**Corollary 3.3 (attainable finite budgets, without an optimality claim).**
For a determining menu of $m$ distinct words the construction above has

$$
\begin{aligned}
H&=|S|+\sum_{j=0}^{m-1}|T_j|
 \ \le\ |S|+\sum_{j=0}^{m-1}4^j,\\
p&=m,\qquad
\ell_P=\sum_{i=1}^{m}|w_i|.
\end{aligned}
\tag{PCA.8}
$$

Empty sums are zero. Any extra required installed latches are added to
$H$. The original reader alphabet, entries, outputs and its own budgets
are unchanged. Under the supplied paid handoff, this gives a two-phase
apparatus for the same code and the whole target.

Proof. There is one counted state for every installed attained prefix
and one for every entry-code latch. Every actual run queries each menu
word once in the chosen order. No further native invocation occurs
between the latch and the fixed reader entry. $\square$

**Remark 3.4 (what the criterion does not decide).** Existence of some
finite determining menu is an exact existence criterion, not an optimum
at prescribed $H,p,\ell_P$. A generating graph might share states or
stop early and use fewer states than (PCA.8). Its installed menu need
not be an optimal sequential querying order. The criterion neither
decides (PCA.7) for arbitrary $\kappa$ nor extracts an effective depth
bound from arbitrary acquired-term program text. Finiteness of each
acquired tree, and termination of a computation on that tree, do not
give one finite observing menu valid uniformly over unbounded trees.
Section 8 supplies a code with exactly this distinction.

## 4. The repeated-partner fiber and its compatible code family

**Definition 4.1 (the entire repeated-partner domain).** For the remaining
results specialize exactly to [NBP, Definition 9.1][NBP]. The cut is
$P=\{L,R\}^3$ and the complete current exterior is perfect to that
depth. Its classes, including all different-class disequalities, are

$$
\{LLL,LRL\}=a,\quad\{LLR\}=b_1,\quad\{LRR\}=b_2,
\quad\{RLL,RRL\}=c,\quad\{RLR\}=b_3,\quad\{RRR\}=b_4.
\tag{PCA.9}
$$

For six pairwise distinct finite values $x$, the current filling is

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{PCA.10}
$$

Write $\mathcal U_*$ for the entire (PCA.2) fiber for this row.
The image grammar, its inverse and [NBP, Proposition 9.3][NBP] supply

$$
\mathcal I=\rho[\mathcal T]
 =\{\beta,E\}\cup\{\langle y,z\rangle:y,z\in\mathcal I\}.
\tag{PCA.11}
$$

A distinct-class filling is an actual image exactly when either all
six values are in $\mathcal I$, or exactly one $x_{b_j}$ is alpha,
its repeated left partner is beta, and all other values are images.
Its actual finite origin is the supplied unique inverse
$u=\delta(\mathscr S(x))$. There is no inverse operation in either
controller phase.

Use the exhaustive entire-fiber partition of [NBP, Proposition 15.2][NBP]:
$\Pi_j$ has $x_{b_j}=\alpha$, its partner beta and all other class
roots branches; $Z_d$ has $x_d=\beta$ and all other class roots
branches; $Z_*$ has all roots branches. A branch class value is an
image. These eleven sets are nonempty and exhaust $\mathcal U_*$.

The target is the original full canonical predecessor row. Denote its
five possible values by $R_0,\ldots,R_4$, as in NBP Proposition 9.3.
On every $Z_d,Z_*$ it is $R_0=R_*$. On $\Pi_j$, the pair of cut holes
at $q_jL,q_jR$, with $(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$, is replaced
by a concrete beta at $q_j$. The other holes and exterior are retained,
the equality partition is restricted to them, and canonical names are
recomputed. In particular the other occurrence of the repeated partner
remains an old hole. All retained disequalities and blocking guards are
part of each fixed output. This whole-target identification is supplied
by NBP Proposition 9.3 and Theorem 10.4, not by the code itself.

**Definition 4.2 (compatible-code template).** For any specified Boolean
function $f$ given by a lawful finite computation on acquired branch
images, prescribe on the entire domain

$$
\sigma_f(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
f(x_a),&u\in Z_{b_3},\\
0,&u\text{ is in any other zero profile}.
\end{cases}
\tag{PCA.12}
$$

Here “other zero profile” includes every $Z_d$ with $d\ne b_3$ and
$Z_*$. In $Z_{b_3}$ the value $x_a$ is a branch image, different from
the beta at $b_3$. Both code values are attained already on the positive
profiles. All references to profile membership in (PCA.12) specify the
function on acquired data; they do not grant a membership query.

**Supplier application 4.3 (one fixed eight-state reader).** Apply
[NBP, Theorem 15.5][NBP] with its parameters

$$
z=0,\quad (\varepsilon_1,\varepsilon_2,\varepsilon_3,
\varepsilon_4)=(0,0,1,1),\quad
S_{15}=\{1,2\},\quad T_{15}=\{3,4\},\quad W_{15}\subseteq\{3\}.
\tag{PCA.13}
$$

Its sufficiency construction with the distinguished test $3$ supplies
one common reader for every function in (PCA.12), including variation
within the entire $Z_{b_3}$. Fix this reader and its two different,
recoverable complete entry states $e_0=\iota(0),e_1=\iota(1)$ once and
for all. It has $K=8$, at most two actual calls and literal sum at most
six: its representative root addresses have length three. These are
credited existing reader results, not new compatibility proofs or new
resource gains in this volume. Every preparer below must latch exactly
$e_{\sigma_f(u)}$, with no reselection of those entries or reader latches.

**Definition 4.4 (context code).** Let $C$ be any finite full ordered
binary context with $n\ge2$ leaf slots, each used once. Their distinct
leaf addresses are $w_1,\ldots,w_n$; they form a prefix-free set.
For any finite tree $B$, including one that does not match the context
shape, define

$$
f_C(B)=\mathbf1_{\{\exists i\in\{1,\ldots,n\}:
                                  r_B(w_i)=\mathsf{branch}\}},
\qquad \sigma_C=\sigma_{f_C},
\qquad \Lambda(C)=3+\sum_{i=1}^{n}(3+|w_i|).
\tag{PCA.14}
$$

Absence and both leaf labels at a slot make that slot's test false.
This is a finite computation on acquired terms. It prescribes exactly
one function on the whole domain, with the original entry $e_{\sigma_C}$.

## 5. A simultaneous whole-fiber upper

**Theorem 5.1 (attaining all three preparation budgets).** For every
context in Definition 4.4, one common-start preparer generates exactly
$e_{\sigma_C}$ on every $u\in\mathcal U_*$ with

$$
H=n+4,\qquad p=n+1,\qquad \ell_P=\Lambda(C).
\tag{PCA.15}
$$

Proof. Install two distinct latches $\widehat e_0,\widehat e_1$ and
$n+2$ distinct running states $D,T,A_1,\ldots,A_n$. Their fixed
literals and all four successors are as follows. Set $A_{n+1}$ to
mean the latch $\widehat e_0$ in this table only; it is not another
running state.

| Running state | Literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR=p_{b_3}$ | $\widehat e_1$ | $A_1$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR=p_{b_4}$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |
| $A_i$, $1\le i\le n$ | $LLLw_i$ | $A_{i+1}$ | $A_{i+1}$ | $\widehat e_1$ | $A_{i+1}$ |

Start at $D$. The subscripted states are separately installed states,
not a counter, computed address, or loop with an uncharged index.
There is no simultaneously live code register. The terminal transition
replaces the running state by the literal entry-code latch.

On the entire fiber, an alpha reply at $b_3$ means $\Pi_3$, whose
prescribed code is one. A beta reply means exactly $Z_{b_3}$, where the
slot tests compute (PCA.14). The occurrence identity [NBP, (NBP.9.7)][NBP]
gives $r_{t_u}(LLLw_i)=r_{x_a}(w_i)$ for every suffix, reached or
absent. Thus the $A_i$ chain gives the exact prescribed code even for
branch values not shaped like $C$.

If the first reply is branch, the remaining possibility for code one
is precisely $\Pi_4$, detected by alpha at $b_4$. All remaining positive
and zero profiles have code zero on that branch. This uses the exhaustive
partition of Definition 4.1; it does not restrict inputs to witness
trees. The representative root $b_3$ is always reached, so its absent
edge is installed but unused. The table nevertheless specifies every
reply edge, including every slot absence.

The initial call followed by all $n$ slot calls costs $n+1$ and
$3+\sum_i(3+|w_i|)$. The other nontrivial path makes two calls of
length three. Since $n\ge2$, every $|w_i|\ge1$, so $n+1\ge2$ and
$\Lambda(C)\ge11>6$. The claimed uniform budgets follow. There are
exactly $n+4$ installed preparation states. The all-beta context
source in §6 attains both the call and literal upper bounds. The paid
handoff then enters the unchanged supplier reader of 4.3. $\square$

## 6. One actual source forces the call and literal bounds

**Definition 6.1 (context replacement witnesses).** Put

$$
B_0=C[\beta,\ldots,\beta],\qquad
B_i=C[\beta,\ldots,\underset{i}{E},\ldots,\beta]
\quad(1\le i\le n).
\tag{PCA.16}
$$

The context's root is an internal node because $n\ge2$. All these
trees are branch images by (PCA.11); they are pairwise different.
At slot $w_i$, $B_0$ has beta and $B_i$ has branch, while the other
slots of $B_i$ have beta. Thus $f_C(B_0)=0$ and $f_C(B_i)=1$.

Choose four further branch images $D_1,D_2,D_4,D_c$, pairwise distinct
and different from every $B_i$, including $B_0$. Such choices exist:
NBP Proposition 15.2 supplies infinitely many branch images, so a finite
forbidden set can be avoided. Define current valuations $x^{(i)}$ by

$$
x_a^{(i)}=B_i,\quad x_{b_3}^{(i)}=\beta,\quad
x_{b_j}^{(i)}=D_j\ (j=1,2,4),\quad x_c^{(i)}=D_c.
\tag{PCA.17}
$$

Every valuation is injective, all its values are images, and hence
NBP Proposition 9.3 supplies its actual finite origin $u_i$. Every
$u_i$ belongs to the entire $Z_{b_3}$ and has full target $R_0$.
Only the prescribed code differs: $\sigma_C(u_0)=0$ and
$\sigma_C(u_i)=1$ for $i>0$. Both occurrences of $a$ contain exactly
the same $B_i$ in each source.

For each slot define its two-occurrence cone

$$
\mathcal C_i=
 \{p w_i v:p\in\{LLL,LRL\},\ v\in\mathcal W\}.
\tag{PCA.18}
$$

These $n$ sets are pairwise disjoint. Any address in $\mathcal C_i$
has length at least $3+|w_i|$.

**Lemma 6.2 (all-address separation locality).** On the pair
$(t_{u_0},t_{u_i})$, a differing actual reply can occur only at an
address in $\mathcal C_i$.

Proof. A word shorter than three is at the common branch skeleton.
Every other word has a unique decomposition $p v$ with $p\in P$.
If its class is not $a$, the entire class value is unchanged. If it
enters either $a$ occurrence, NBP's actual occurrence identity reduces
the reply to the suffix $v$ in $B_0,B_i$. Their sole replacement is
at $w_i$. Outside its descendant cone the finite trees agree at every
constructor and every blocking leaf. At a proper prefix of $w_i$ both
have the context's branch. Therefore only $v=w_i z$ can differ.
This argument includes nonexistent addresses, leaf continuations,
both leaf labels and every finite deep suffix. It asserts necessity
of the cone, not that all queries in that cone are informative.
$\square$

**Theorem 6.3 (independent call and literal lower bounds).** Every finite
accurate common-start preparer for $\sigma_C$ on the entire
$\mathcal U_*$ satisfies, on the single source $u_0$,

$$
q_P(u_0)\ge n+1,\qquad
\ell_P(u_0)\ge3+\sum_{i=1}^{n}(3+|w_i|)=\Lambda(C).
\tag{PCA.19}
$$

Consequently every uniform upper budget has $p\ge n+1$ and
$\ell_P\ge\Lambda(C)$, whatever larger finite state or other
preparation budgets are allowed.

Proof. Compare the terminating run on $u_0$ with the run on each
$u_i$. Their required latches differ. If no query along the $u_0$
path had different replies on that pair, induction from the common
start would give the same entire path and the same latch on $u_i$.
Hence for each $i$ some query on the $u_0$ path belongs to
$\mathcal C_i$, by Lemma 6.2. Disjointness forces at least $n$
different visits, with total literal contribution at least
$\sum_i(3+|w_i|)$.

One additional visit is forced on this same path. Starting from
$x^{(0)}$, keep $x_a=B_0$ and $x_{b_j}=D_j$ for $j=1,2,4$, but
replace $x_c$ by beta and $x_{b_3}$ by alpha. The resulting six values
are distinct. They meet NBP Proposition 9.3's positive alternative
$3$, so they give an actual finite origin $u_+$ in $\Pi_3$. Its full
target is $R_3$ and its prescribed code is one. The currents of $u_0$
and $u_+$ differ only in the $c$ and $b_3$ class values. Equal replies
all along the $u_0$ path would again force the same latch. Some query
on that path must therefore enter a $c$ occurrence or the $b_3$
occurrence. Every such word has length at least three and lies outside
all the $\mathcal C_i$. It is an additional counted visit.

Adding these contributions proves both inequalities on one actual
execution. No worst costs from different sources have been added.
The argument uses neither a tree-shaped controller nor a restriction
of the upper-domain fiber. $\square$

## 7. A global installed-menu state lower bound

**Lemma 7.1 (two additional mandatory class cones).** Every accurate
preparer for any code of template (PCA.12) has an installed running
state whose address enters the $b_3$ occurrence and another whose
address enters the $b_4$ occurrence.

Proof. Choose $x_c=\beta$ and five pairwise distinct branch image
values for $a,b_1,b_2,b_3,b_4$. Their filling is an actual zero source
$z\in Z_c$ by NBP Proposition 9.3. It has code zero under (PCA.12).
Replace only $x_{b_3}$ by alpha. The resulting filling is an actual
$\Pi_3$ source, with code one; distinctness and the repeated beta
partner are preserved. These two current trees agree at every word
outside the $b_3$ occurrence cone, by the same complete occurrence
analysis as Lemma 6.2. Without an installed query in that cone their
entire menu replies would agree, contradicting Lemma 2.3 and their
different required latches.

Instead replace only $x_{b_4}$ in the zero source by alpha. This gives
an actual $\Pi_4$ source of code one, differing only in the $b_4$
cone. The same reasoning requires an installed query there. The two
cones are disjoint. This is a restriction of a lower-bound comparison
to actual sources, not a new promise on the full domain. $\square$

**Theorem 7.2 (independent state lower bound and exact hierarchy).**
Every finite accurate preparer for $\sigma_C$ on the entire original
fiber has

$$
|V|\ge n+2,\qquad |\mathcal B|\ge n+4.
\tag{PCA.20}
$$

Together with Theorems 5.1 and 6.3 this proves the simultaneous exact
preparation frontier (PCA.15): every feasible budget vector dominates
$(n+4,n+1,\Lambda(C))$ coordinatewise, and that vector is attained.
Increasing either of the other two preparation coordinates cannot
reduce any one of these minima. The reader remains the credited
$K=8,q_R\le2,\ell_R\le6$ reader with its original entry.
In NBP Definition 14.2's seven-coordinate notation this attains
$(2,n+4,8,n+1,\Lambda(C),2,6)$ with the specified encoder held fixed.

Proof. For each $i$, Lemma 6.2 and the different-code sources $u_0,u_i$
force an installed address in $\mathcal C_i$. These are $n$ distinct
running states because the cones are disjoint and each state has one
fixed address. Lemma 7.1 forces two more running states, in $b_3$ and
$b_4$, outside every $a$ cone and each other. Thus $|V|\ge n+2$.
Both codes occur on $\Pi_1$ and $\Pi_3$, so their different original
entries require two distinct terminal latches. All these states count,
giving $|\mathcal B|\ge n+4$.

This argument is about the installed menu of an arbitrary successful
graph. It does not unroll its paths or count separate copies of shared
states. Convergence, cycles, repeated fixed words, queries at other
addresses and unused installed states cannot remove a required cone
state. In particular, the state bound remains valid when call or
literal budgets increase. The other two coordinatewise lower bounds
are Theorem 6.3, and their simultaneous upper is Theorem 5.1. $\square$

**Remark 7.3 (content of the hierarchy).** The parameter is an arbitrary
finite full ordered context, not a successive small numerical example.
Every such context supplies independent actual source variations in
its leaf-slot cones. Its number of slots controls two exact resources;
their original address lengths control the third. A slot ancestor
cannot replace a slot test on these witnesses, since its reply remains
branch. The proof does not import a Boolean query count: it proves
the transfer for every native address, both repeated occurrences and
the full original image domain. No restriction to the displayed
witness family is used in the upper.

## 8. Finite acquired-term computation without finite native generation

**Definition 8.1 (the alpha-containing acquired term).** For a finite
branch image $B$, prescribe

$$
f_\infty(B)=\mathbf1_{\{B\text{ contains an alpha leaf}\}},
\qquad \sigma_\infty=\sigma_{f_\infty}
\tag{PCA.21}
$$

using exactly (PCA.12) on all other profiles. Structural inspection of
an acquired finite term decides this predicate: beta contributes false,
alpha true, and a pair takes the disjunction of its children's values.
This is a statement about a finite mathematical computation on already
acquired data. Its workspace and access are not supplied to Definition
2.2. The original eight-state reader of 4.3 still serves this exact
code, with the same $e_0,e_1$ and two-call bound.

**Theorem 8.2 (no finite installed preparer for the original code).**
No finite installed stationary fixed-address common-start preparer
generates $e_{\sigma_\infty(u)}$ correctly on the whole
$\mathcal U_*$. This holds even if no uniform preparation call bound
is specified and only sourcewise termination is demanded.

Proof. Fix any finite installed menu $M$ of a proposed preparer. Let
$L=\max(\{0\}\cup\{|v|:v\in M\})$ and choose an integer $d>L$
with $d\ge1$. Let $B^-$ be the complete ordered binary tree with all
leaves beta at depth $d$. Choose one of these leaf occurrences and
replace its beta by $E$, obtaining $B^+$. Both are finite branch
images by (PCA.11). The first has no alpha leaf and the second has
one. Every address of length strictly less than $d$ reads branch in
both trees.

Choose four other branch images for $c,b_1,b_2,b_4$, pairwise distinct
and different from $B^-,B^+$. In both current valuations set
$x_{b_3}=\beta$, set $x_a$ respectively to $B^-$ and $B^+$, and keep
those four values fixed. The valuations are injective image fillings;
NBP Proposition 9.3 gives two actual finite origins $u^-,u^+$ in the
entire $Z_{b_3}$. Both have the same full target $R_0$. Their prescribed
codes, and hence their required complete entries, differ.

For every $v\in M$ shorter than three the current reply is the common
exterior branch. Otherwise write $v=pw$ with $p\in P$. In a class other
than $a$ the entire subtree value is the same. In either occurrence of
$a$, the actual occurrence identity gives the reply of $B^-$ or $B^+$
at $w$. Here $|w|\le|v|\le L<d$, so both replies are branch. Thus
the two actual currents have identical replies at every installed
word, including words that are absent in any unchanged class. This
covers the whole menu, rather than a chosen shallow query policy.

Lemma 2.3 forces identical paths and the same latch, contradicting
the different prescribed entries. If the path never terminates,
sourcewise correctness already fails. A cycle cannot wait for a new
reply from a stationary register, and the fixed-state model cannot
generate a new longer address. No uniform call assumption was used.
$\square$

**Corollary 8.3 (the obstruction is inside a fixed target fiber).**
The code in (PCA.21) is a lawful acquired-term code, compatible with
the old reader, but has no determining finite menu of Theorem 3.2.
The obstruction occurs between sources with the same $F=R_0$.
It is therefore the cost of preserving this specified extra code,
not an impossibility of recovering $F$ with freely reselected encoders.

Proof. For every finite menu the construction in Theorem 8.2 gives an
equal-observation pair with different prescribed code and the same
whole target. This violates (PCA.7). For comparison within the same
compatible-code template, choose instead $f\equiv0$. Then testing
$b_3$ and, on a non-alpha reply, $b_4$ generates the prescribed bit
with finitely many fixed states and at most two paid calls; on either
alpha reply it latches $e_1$, otherwise $e_0$. All four successors
can be fixed accordingly. Definition 4.1 shows on the entire domain
that the only alpha cases are $\Pi_3,\Pi_4$, exactly the code-one
cases for that different encoder. The supplier reader then recovers
the full target. This comparison expressly changes the encoder; it
does not generate $\sigma_\infty$. $\square$

## 9. Suppliers, overlap, and the precise remaining obligations

**Convention 9.1 (attribution and parameter correspondence).** The
following are the suppliers and the scope in which they are used.

| Supplier | Exact role and boundary |
| --- | --- |
| [NBP, Definitions 1.1–1.2 and 9.1; Assumptions 9.2 and 10.6; Proposition 9.3][NBP] | Original ordered alpha/beta grammar, substitution, actual acquisition contract, complete repeated-partner inverse fiber, all five complete canonical predecessor rows and actual finite inverses. These are reused throughout. |
| [NBP, (NBP.9.7), Proposition 10.2 and Theorem 10.4][NBP] | Every-address occurrence identity, actual assignment/image conditions and full-target bridge. The $x$ in each witness is an injective valuation satisfying those actual conditions; its current tree is $\rho\delta(\mathscr S(x))$. |
| [NBP, Proposition 12.5; Definitions 13.1 and 14.2; Assumption 14.1][NBP] | Stationary no-revisit principle, actual literal sums, counted running/latch convention, one common start and paid code-only handoff. Our $H,p,\ell_P$ are precisely its preparation coordinates; its $K,q,\ell_R$ remain reader coordinates. |
| [NBP, Theorem 14.4 and Assumption 14.9][NBP] | Jointly reselected preparation/reader transfer and its operational limits. It does not generate a specified arbitrary encoder, and is not used as a fixed-code normalization. |
| [NBP, Proposition 15.2, Theorem 15.5 and Convention 15.9][NBP] | Exhaustive entire-profile partition, infinite choice of distinct branch images, and the original-code compatibility supplier instantiated in (PCA.13). Compatibility is inherited; preparation is the obligation proved here. |
| [Native passive service realization, Definitions 1.1–1.5 and Theorem 1.6][NPS] | Related finite unfolding/materialization principle, with a complete retained trace and an original effective service. That model does not supply our trace-free latch state budget, source-dependent code function, or prices. No current compilation of its declarations is claimed. |
| [Native finite-menu minimal memory, §§1–2][FMM]; [Native representative-reply normal form, §1][RRN] | Related finite-menu and paid source-blind export terminology. Their source is the height-bounded $\{\langle\alpha,v\rangle:h(v)\le D\}$ family and their target is a late selected reply. Neither is the unbounded complete one-image predecessor-row task here. |
| [Original-control record acquisition, §1 and its remaining-interface discussion][OCRA]; [Original-control instrument boundaries, opening source contract and §1][OCIB] | Distinction between actual history, retained data and an operational acquisition interface. Their controls are continuous probability/phase histories; no native state, call or literal bound is transferred from them. |

**Convention 9.2 (mature background and bounded literature scope).**
Deterministic query indistinguishability is background: equal acquired
replies along a common path cannot determine different required answers.
For a readable example, Ronald de Wolf, *Quantum Computing: Lecture
Notes*, [arXiv:1907.09415, §2.4.1][DW], explains the deterministic
Deutsch–Jozsa lower argument by the answer remaining undetermined after
the all-zero partial transcript. Only that indistinguishability
principle is credited here. Its promise, query model and numerical
bound are not premises for (PCA.15) or (PCA.20). Moore-machine
stationarity is supplied in the exact native form by NBP Proposition
12.5 and reused in Lemma 2.3.

Harry Buhrman and Ronald de Wolf, *Complexity Measures and Decision
Tree Complexity: A Survey*, *Theoretical Computer Science* 288(1),
21–43, 2002, is a bibliographic reference verified from [de Wolf's publication
list][BDW]. No unread theorem from that survey is used as a proof
premise. The arXiv exposition above was read for the stated elementary
example. No Boolean, XOR, spectral, graph or quantum numerical frontier
is imported.

The overlap search was bounded to the owner, native/acquisition theory
texts and the relevant FibonacciAtomic source/Blueprint descriptions,
using prescribed-code, common-start, generated-code, fixed-address and
finite-observation terms. The neighboring finite-menu, passive-service,
representative-reply and continuous-control interfaces in 9.1 are the
relevant comparisons read. This is not global literature coverage or
evidence of worldwide novelty. The finite-observation equivalence is
an elementary deterministic-table deduction. The native cone transfer,
the simultaneous arbitrary-context preparation optimum, and the
compatible nongenerable code are `repo-derived` ordinary-paper
deductions relative to the cited native suppliers.

**Remark 9.3 (meaningful tests and residual scope).** For every context,
(PCA.17) gives actual same-target sources requiring different original
codes, so the slot obligation is not a reformulation of target
classification. The $Z_c/\Pi_3$ and $Z_c/\Pi_4$ pairs force two
additional installed cones independently of the slot comparisons.
The negative run in Theorem 6.3 would falsify any claimed smaller call
or literal budget: it must distinguish every one-slot replacement and
the actual $\Pi_3$ replacement on that same execution. Theorem 8.2
gives a falsifying pair for every proposed finite installed menu.
These structural families give all-address proofs, without member
enumeration, an executable search or a finite sample replacing the
whole domain.

The exact result in §7 concerns the preparation coordinates for this
prescribed context-code family. It is not an arbitrary-budget
classification for every $\kappa$, an algorithm deciding arbitrary
observational constancy, or a code-preserving deep-padding theorem.
NBP Proposition 15.8's refutation of universal code-preserving padding
remains in force. The deep pair of §8 is constructed for its particular
alpha-containing code and gives opposite codes, not padding that
preserves an arbitrary original code.

Neither a finite transition table nor acquired-term decidability
constructs the actual acquisition, authentication, stationary native
service, paid export, isolation or entry mechanism. If those services
or any source-bearing field change, the operational conclusion must be
rechecked. No free archive, selector, phase bit, counter, computed
address, duplicated live code, output decoder, or later code reaccess
is used in the stated apparatus. The original reader and whole-row
halts remain installed and counted separately from preparation. Their
alphabet sizes do not automatically combine into a physical memory,
time, energy or total table-byte optimum. The full continuing native
relational-fiber research and its broader realization obligations
remain open beyond this finite package.

[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[NPS]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativePassiveServiceRealization.md
[FMM]: FIB_NATIVE_FINITE_MENU_MINIMAL_MEMORY.md
[RRN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REPRESENTATIVE_REPLY_NORMAL_FORM.md
[OCRA]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md
[OCIB]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md
[DW]: https://arxiv.org/html/1907.09415#Ch2.S4.SS1
[BDW]: https://homepages.cwi.nl/~rdewolf/#PublSurveys

## 追加锚（本行以下为增补区）
