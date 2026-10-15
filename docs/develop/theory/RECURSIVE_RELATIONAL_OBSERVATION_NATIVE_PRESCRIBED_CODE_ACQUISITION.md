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

## 10. A certificate-relative finite basis with the original reader fixed

**Assumption 10.1 (unchanged task and a supplied determining certificate).**
Use the arbitrary nonempty full fiber of Assumption 1.2, the prescribed
code and complete recoverable entry of Definition 2.1, and the preparation
apparatus of Definition 2.2. In particular, the original reader's entire
installed table, alphabet, running/halt partition, whole-row halt labels
and entry map remain fixed. The target is the complete canonical
$F(u)=R_P(u)$, with all occurrence holes, retained equalities,
different-class disequalities, canonical renaming and blocking guards.
All finite origins in the original fiber remain in the domain.

A supplied valid finite determining certificate is a finite menu $M$
together with its well-defined attained-value assignment

$$
\chi:O_M[\mathcal U]\longrightarrow S,
\qquad \chi(O_M(u))=s(u)=\iota(c(u)).
\tag{PCA.22}
$$

One can equivalently supply $M$ and the validity assertion (PCA.7);
then (PCA.22) defines the unique assignment. No method for finding $M$
or establishing its validity from arbitrary program text is assumed.
The complete values in $S$ are the original entries, not newly selected
names for target classes. The assignment is mathematical task data;
it is not a readout port or a decoder callable by a running state.

**Definition 10.2 (row coordinates and an explicit actual-address basis).**
Write $R_*=(C_*,\pi_*)$, let $H$ be its reached cut support and $D$ its
class set. Use NBP Definition 10.1's legal valuation notation
$\mathscr F_*(x)=C_*[(x_{[p]})_{p\in H}]$ and
$\mathcal X_* =\{x:D\to\mathcal T:(\forall d\ne e,\ x_d\ne x_e)
\land\mathscr F_*(x)\in\mathcal I\}$, where $\mathcal I=\rho[\mathcal T]$.
Its actual origin is $u_x=\delta(\mathscr F_*(x))$; this is the supplier's
bijection to the original $\mathcal U$, not an inverse port available
to a controller. For a class $d$, choose its shortest actual occurrence

$$
a_d=\underset{p\in H,\,[p]=d}{\operatorname{argmin}}\ (|p|,p).
\tag{PCA.23}
$$

The tie order is the public lexicographic order. This is NBP Definition
13.1's convention; it does not change the canonical class name.
Traverse each word of $M$ in the finite exterior. If traversal first
enters an occurrence hole $p$, write that word uniquely as $pw$.
Put

$$
\begin{aligned}
b&=\max\bigl(\{0\}\cup
 \{|w|:pw\in M,\ p\in H\text{ is its first hole}\}\bigr),\\
B_b&=\{\varepsilon\}\ \cup\
 \{a_dw:d\in D,\ w\in\mathcal W,\ |w|\le b\}.
\end{aligned}
\tag{PCA.24}
$$

Thus $B_b$ is finite, consists only of original absolute native words,
and depends only on the original row and the supplied certificate.
It is independent of the competing preparation table and every budget.
If $D=\varnothing$, it is $\{\varepsilon\}$. A hole at the root has
$a_d=\varepsilon$. Words stopped by an exterior leaf, including all
extensions in its absent cone, contribute no residual depth to $b$.

For a legal class valuation $x$, let $\eta_b(x)$ consist of the
four-valued actual replies of each $x_d$ at relative words of length at most $b$.
Early leaves stop further descent and give absent at every strict
descendant. The tuple is a mathematical finite profile, not accessible
configuration. Two actual sources with the same profile have the same
replies on $M$, the same original code and the same complete entry.
They also have the same whole target, by NBP Theorem 10.4: the profile
includes the class roots, which determine the predecessor row on this
fixed current-row one-image fiber. That supplier is used for the whole
row, not replaced by a root-type target.

**Theorem 10.3 (entire preparation upper-budget region on a fixed basis).**
Under Assumption 10.1, restricting every preparation literal to $B_b$
preserves the entire feasible region in installed states, calls and
executed literal sum. More precisely, fix any finite installed
preparation alphabet $\mathcal B=V\sqcup\widehat S$, its partition,
its literal latch values and its common start $b_0$, including any
additional required installed latches. If a table on those very states
generates the original $s(u)$ on every $u\in\mathcal U$ with uniform
upper budgets $p,\ell$, another table with all literals in $B_b$ does
so on exactly the same alphabet, partition, latches and start, with
upper budgets no larger than $p,\ell$. No state is removed or added.
The original reader and its entire table are unchanged.

Consequently, for every $H,p,\ell$, unrestricted native preparation
and $B_b$-restricted preparation are equivalent under the same three
upper budgets. If the fixed reader has separate uniform call and
literal upper budgets, those bounds remain valid without alteration.
This last assertion is about separate phase coordinates. A bound on
the sum of the two phases on each same execution requires Theorem 13.1.

The proof of this theorem is given in §12 after the actual-image
attainment bridge. It compares the new preparation on $u$ with the
old preparation on a suitable actual source in the same finite profile.
It makes no assertion that their paths or costs agree, or improve,
on each same original $u$.

## 11. Exact finite-prefix attainment inside the actual image fiber

**Definition 11.1 (finite image profiles and their whole-term negatives).**
Fix any inclusive relative depth $b\ge0$. For each class $d$, form a
finite prefix pattern that exposes every node through depth $b$, stops
at each early leaf, and retains that leaf's entire absent cone. A branch
at depth $b$ is represented by a live name $z_{d,w}$, where $w$ is its
relative occurrence address. Its observed reply is branch; its hidden
value is required to be a branch image. A leaf at depth $b$ is retained
as that literal leaf. All branch constructors at smaller depth are
retained. Call the resulting finite free term $T_d$.

Names for different pairs $(d,w)$ are independent. Every occurrence of
one class in $C_*$ uses exactly the same $T_d$ and exactly the same
names. There is no requirement that distinct live names have distinct
values. The required distinctness is the entire conjunction

$$
\Delta=\bigwedge_{d\ne e} T_d\ne T_e.
\tag{PCA.25}
$$

The two sides are whole class terms, including all fixed finite pieces.
They are not replaced by childwise inequalities. Define a syntactic
image predicate $J$ on these terms by

$$
\begin{aligned}
J(\alpha)&=\mathsf{false},& J(\beta)&=\mathsf{true},&
J(z_{d,w})&=\mathsf{true},\\
J(\langle A,B\rangle)&\Longleftrightarrow
 (A=\beta\text{ literally and }B=\alpha\text{ literally})
 \ \lor\ (J(A)\land J(B)).
\end{aligned}
\tag{PCA.26}
$$

A live name is a branch, so it is neither of the two literal leaves
in the first disjunct. Expand fixed grounds in the free ordered
$\alpha/\beta$ signature. Retain precisely those pattern tuples for
which

$$
J(C_*[(T_{[p]})_{p\in H}])\quad\text{and}\quad
T_d,T_e\text{ have unequal syntax whenever }d\ne e.
\tag{PCA.27}
$$

Denote this finite set of retained profiles by $\Omega_b$. These are
finite syntactic tests on bounded patterns, not tests of an unknown
acquired-term program. The exterior is kept literally, so all its
concrete leaves, repeated holes and blocked public cut members remain.

**Theorem 11.2 (actual attainment and simultaneous deep live filling).**
The retained profiles are exactly the profiles of the entire actual
fiber:

$$
\Omega_b=\{\eta_b(x):x\in\mathcal X_*\},
\qquad
\mathcal X_*\cong\mathcal U
\text{ as in NBP (NBP.10.3).}
\tag{PCA.28}
$$

For every $\eta\in\Omega_b$ and every finite $L\ge0$, there is one
actual legal valuation $x^{\eta,L}$ with this profile in which all
live names are simultaneously filled by finite non-atomic image trees
of minimum leaf depth greater than $L$, while every whole-class
negative in (PCA.25) holds. Its filled current tree has the actual
finite inverse

$$
t^{\eta,L}=C_*[(x^{\eta,L}_{[p]})_{p\in H}]
          =\rho u^{\eta,L},\qquad u^{\eta,L}=\delta(t^{\eta,L})\in\mathcal U.
\tag{PCA.29}
$$

All repeated class occurrences use one value. No source-size or depth
promise is imposed on $\mathcal U$.

Proof. Reuse the disjoint native image grammar
$\mathcal I::=\beta\mid E\mid\langle\mathcal I,\mathcal I\rangle$
and its unique inverse, supplied by NBP Proposition 9.3 and the source
cited there. Every branch subtree of an image is itself an image; the
only possible nonimage subtree is the literal alpha. This is the
subtree fact used in NBP Proposition 10.2.

For any assignment of branch images to the live names, (PCA.26) is
exact for image membership of a free term. Indeed, its leaf and live
cases are exact. At a pair, equality with $E$ requires its two children
to be the literal beta and alpha: a live name or a pair has branch
root and cannot become either leaf. The other image alternative is
exactly a pair of images. Induction gives (PCA.26) for the whole term.
Thus (PCA.27)'s first condition makes every such live filling an image.
This is an application of the existing image grammar, not a new image
or disunification supplier.

An actual legal valuation has a unique depth-$b$ decomposition of the
stated form. Each of its live branch subtrees is an image. Image
membership gives the first condition in (PCA.27). An identical pair of
syntactic class terms would evaluate equally under every assignment,
contrary to its actual class disequality. Hence every actual profile
is retained.

Conversely, for a retained pattern apply [Retained Literal Root Depth,
Theorem 2.2][LRD] directly to the finite list (PCA.25), with intrinsic
rank one for every remaining name and minimum leaf depth greater than
$L$. All sides are free terms over the common names, with fixed grounds
literally expanded, and every listed pair has unequal syntax by
(PCA.27). That theorem supplies one simultaneous finite tuple,
including all negatives involving closed ground classes. Rank one
implies membership in $\rho[\mathcal T]$; non-atomicity and the supplied
deep-leaf property give the required branch images. If there are no
live names, the empty tuple works: every class is a fixed finite ground
and the retained negatives are already unequal grounds.

The filling therefore has its exact prescribed branch/leaf/absent
profile, all different-class disequalities, and an image whole tree.
NBP's legal-row bijection and unique inverse give (PCA.29), with the
complete current row exactly $R_*$. This proves both directions of
(PCA.28) and the simultaneous strengthening. One may make these choices
for all finitely many retained profiles; no relation between their
separate actual origins is required. $\square$

**Proposition 11.3 (closed pieces and the scope of live padding).**
Theorem 11.2 keeps an early leaf exactly and never fills below it. A
fully exposed $E=\langle\beta,\alpha\rangle$ is a closed ground piece,
not a live branch that may be made leafless. A branch observed only
at the frontier may be replaced by a deep branch image because its
children are outside that profile. In particular this replacement
does not preserve an arbitrary code whose certificate observes those
children; that certificate requires the larger profile in (PCA.24).

For $b=0$, a branch class is one live name, while an alpha or beta
class is a ground. For zero classes there is just the concrete exterior
and the empty tuple; nonemptiness of the fiber makes it an image and
provides its unique inverse. The empty cut and blocked-cut cases are
included. A root cut is treated as its one class at absolute address
$\varepsilon$.

Proof. These statements follow from the unique prefix decomposition
and the literal image test in Definition 11.1. A recorded alpha right
child and beta left child retain $E$ literally in (PCA.26); neither
can be changed by assigning a live name. An absent reply is justified
by an actual earlier leaf and persists under every assignment. Only
nodes with branch reply at the last observed level receive live names.
The zero-class statement follows from (PCA.29) with no variables.
$\square$

## 12. All-address paid recoding without changing installed states

**Definition 12.1 (one actual word and one four-reply map per old word).**
Fix $b$ and $B_b$ of Definition 10.2. For every original finite native
word $v$, define a word $h_b(v)\in B_b$ and a map
$g_{b,v}:\mathcal A\to\mathcal A$ as follows.

If exterior traversal of $v$ never enters a reached hole, let $z_v$
be its exterior-determined reply, including any forced absence. Put
$h_b(v)=\varepsilon$ and $g_{b,v}(z)=z_v$ for all four $z$.

If traversal first enters hole $p$ of class $d$, write $v=pw$.
For $|w|\le b$, put $h_b(v)=a_dw$ and let $g_{b,v}$ be the identity.
For $|w|>b$, let $w_{\le b}$ be its length-$b$ prefix and put

$$
\begin{aligned}
h_b(v)&=a_dw_{\le b},\\
g_{b,v}(z)&=
\begin{cases}
\mathsf{branch},&z=\mathsf{branch},\\
\mathsf{absent},&z\in\{\alpha,\beta,\mathsf{absent}\}.
\end{cases}
\end{aligned}
\tag{PCA.30}
$$

Every new word is no longer than the old word, because $a_d$ is a
shortest occurrence of the same class. These are static substitutions
into a finite installed table. No running operation concatenates,
truncates, selects or decodes an address.

**Lemma 12.2 (one actual witness for all submitted words).**
For any finite native menu $N$, let
$L=\max(\{0\}\cup\{|v|:v\in N\})$. For every actual $u$ with profile
$\eta=\eta_b(x)$, the single actual witness $u^{\eta,L}$ of Theorem
11.2 satisfies, simultaneously for all $v\in N$,

$$
r_{\rho u^{\eta,L}}(v)
 =g_{b,v}\bigl(r_{\rho u}(h_b(v))\bigr).
\tag{PCA.31}
$$

It has the same original code, complete entry and whole predecessor
row as $u$ when $b$ comes from its determining certificate.

Proof. Outside holes both sides have the exterior's fixed reply. For
$v=pw$ with $|w|\le b$, the every-address occurrence identity reads the
same suffix in either occurrence of the class, and both sources have
the same profile. For $|w|>b$, consider the actual reply at
$w_{\le b}$ in that class. If it is alpha or beta, every strict
continuation is absent. If it is absent, an earlier leaf already blocks
all continuations. If it is branch, it is a live name in the profile.
In $x^{\eta,L}$ that name is filled by a tree of minimum leaf depth
greater than $L$. The remaining suffix has length $|w|-b\le L$,
so the endpoint is a reached branch. These are exactly the four cases
of (PCA.30). One LRD filling serves the entire menu, including all
occurrences of repeated classes and all absent continuations.

The witness and $u$ agree on $M$, so (PCA.22) keeps their original
codes and entries. They have the same class roots, so NBP Theorem
10.4 keeps their complete predecessor rows. The inverse in (PCA.29)
makes this an actual-source comparison. $\square$

**Proof of Theorem 10.3.** Let $a(v),N(v,z)$ be the old preparation
table. Include all its installed running words, even unused ones, in
the finite menu of Lemma 12.2. On precisely the old alphabet install

$$
a'(v)=h_b(a(v)),\qquad
N'(v,z)=N\bigl(v,g_{b,a(v)}(z)\bigr).
\tag{PCA.32}
$$

Keep every latch and its literal complete entry, the running/latch
partition and the common start $b_0$ exactly. All four successors are
installed, including unattained replies. A source-independent word is
replaced by a genuine root call followed by its forced old successor;
it is not bypassed by a silent edge. In particular $\varepsilon$ still
costs one invocation. No extra selector, counter, trace or working
configuration is installed.

Fix an arbitrary actual $u$ with profile $\eta$. Compare the new run
on $u$ with the old run on the actual $u^{\eta,L}$ of Lemma 12.2.
Their common start is the same. At an equal running state (PCA.31)
and (PCA.32) give the same next state. Induction gives precisely the
same ordered running-state visits and the same terminal latch. The
old run terminates correctly with $\widehat{s(u^{\eta,L})}$, which
is $\widehat{s(u)}$. Its call count is identical to the new run's;
each new word on this common state path is no longer. Thus

$$
q_{P'}(u)=q_P(u^{\eta,L}),\qquad
\ell_{P'}(u)\le\ell_P(u^{\eta,L}).
\tag{PCA.33}
$$

The old uniform upper bounds apply on this actual witness in the full
original fiber. Hence the new bounds hold for every original $u$.
The installed state cardinality is exactly unchanged, including unused
states and unused latches. If $b_0$ is a latch, both runs stop there
without a call and the same argument applies. A terminating run cannot
revisit a running state by Lemma 2.3; no assumption of an acyclic union
graph, no state unfolding and no elimination of shared successors has
been used. Cycles on unused transitions remain permitted.

Handoff enters the same original $s(u)$ in the untouched original
reader. It therefore retains that reader's correctness on $u$ and any
of its separately valid uniform phase bounds. The reverse implication
is immediate because all words in $B_b$ are legal original native
words. This proves the exact upper-region assertion. $\square$

**Definition 12.3 (the finite paid word task).** On the finite family
$\Omega_b$, the response to $a_dw\in B_b$ is the original reply of
class $d$ at $w$ in the profile. The response to $\varepsilon$ is the
root reply of the current tree: it is fixed by the exterior unless
there is a root hole, in which case it is that class's root reply.
Coincident spellings denote the same actual word and the same reply.
Let $s_\eta$ be the complete original entry determined by (PCA.22).

The finite task on a prescribed installed alphabet is to assign each
running state one word of $B_b$ and four successors, keeping the
common start and literal latches, such that for every $\eta\in\Omega_b$
the induced path terminates at $\widehat{s_\eta}$. Charge every
running visit one call and charge the sum of the actual absolute word
lengths. Charge every installed state once, including unused ones.
There is no operation reading $\eta$, $s_\eta$ or the response row
as a tuple. At runtime only the table's one paid native word is read.

**Theorem 12.4 (exact arbitrary-budget finite task, conditional on the
certificate).** For every installed preparation alphabet and common
start, and every $p,\ell$, the finite paid word task of Definition
12.3 is feasible within those budgets if and only if original native
preparation is feasible within the identical state/call/literal upper
budgets for the prescribed code and fixed reader entry.

Proof. Theorem 10.3 gives necessity with the same installed states.
The new table's reply at every word of $B_b$ depends only on $\eta$,
so its entire path, latch and prices are those of Definition 12.3.
For sufficiency, install the finite task's words and four successors
literally. Theorem 11.2 places every actual original in one retained
profile and attains every retained profile by actual originals.
Induction gives exactly its finite task path, literal entry and
charges. The untouched reader returns the whole target by Assumption
10.1. Shared states and cycles are retained rather than replaced by a
decision tree. $\square$

This theorem is a deduction from the actual-image filling and paid
state-local recoding above. Its finite formulation alone is not the
attainment argument, and does not establish validity of an arbitrary
program's proposed certificate.

## 13. Correlated two-phase costs and the separate design-variable reader

**Theorem 13.1 (immutable-reader correspondence for same-run objectives).**
Under Assumption 10.1 let $M_R$ be the set of all words installed in
the fixed reader's running states, including unused states. Replace
$M$ in (PCA.24) by $M\cup M_R$, obtaining a depth $b_R$ and basis
$B_{b_R}$. This basis may depend on the fixed reader's observations,
but is independent of the competing preparer and every budget.

For every successful preparer there is a preparer on exactly its same
states, partition, start and literal latches, with words in $B_{b_R}$,
while the reader is entirely unchanged. For every actual $u$ there is
one actual $u^\dagger$ in the original full fiber with the same code,
complete entry and whole target such that

$$
\begin{aligned}
q_{P'}(u)&=q_P(u^\dagger),&
\ell_{P'}(u)&\le\ell_P(u^\dagger),\\
q_R(u)&=q_R(u^\dagger),&
\ell_R(u)&=\ell_R(u^\dagger).
\end{aligned}
\tag{PCA.34}
$$

The unchanged reader also follows the same ordered states and halt
on $u$ and $u^\dagger$. Thus this basis preserves feasibility of
uniform separate-coordinate bounds and same-run bounds such as
$q_P(u)+q_R(u)\le T$ and $\ell_P(u)+\ell_R(u)\le A$ for all actual
$u$, and their simultaneous imposition. More generally the same
comparison works for a coordinatewise nondecreasing constraint on
these four execution costs.

Proof. Use Theorem 11.2 at depth $b_R$ and the maximum of the old
preparer's installed word lengths. Its witness $u^\dagger$ has the
same replies as $u$ at every installed reader word: if a reader word
enters a hole, its suffix has length at most $b_R$ by definition;
otherwise its reply is exterior-determined. The original entry is
also unchanged. Induction through the fixed reader therefore gives
its same state path and charges on $u,u^\dagger$.

Apply (PCA.32) only to the preparation table. Lemma 12.2 compares its
new run on $u$ with its old run on this very same $u^\dagger$, yielding
the first line of (PCA.34). Combining the two lines uses one actual
origin, not separate maximizers for preparation and reading. The
reverse feasibility implication uses inclusion of basis words among
native words. The argument does not compare the old and new
preparation costs on the same $u$. $\square$

**Definition 13.2 (both tables as design variables, original entry fixed).**
Keep the original acquired-term code $c$, its attained literal values,
the same complete injective entry map $\iota$, the reader alphabet and
running/halt partition, and the whole-row output assigned to every
halt. Keep the preparation alphabet, its partition, latches and start.
Allow both graphs' running literals and four-successor functions to
be chosen. Acquisition, authentication, paid handoff, access isolation
and same-register continuity remain the supplied services of §1.
In particular this permission to redesign the reader is stronger than
Assumption 10.1 and is stated separately.

**Theorem 13.3 (both-table-design correspondence on the certificate basis).**
Under Definition 13.2, the smaller basis $B_b$ of (PCA.24), depending
only on the row and the code certificate, preserves the whole joint
upper-budget region of both table designs. Both tables may be restricted
to words in $B_b$ without changing either installed alphabet,
partition, the common preparation start, any literal entry value or
any whole-row halt label. The preserved execution objectives include
all separate call/literal coordinates and the same-run total call and
literal bounds in Theorem 13.1.

Proof. Take any feasible pair of tables. Let $L$ be the maximum length
of all installed running words in both phases, including unused words.
For each actual $u$ use the single $u^{\eta,L}$ of Theorem 11.2.
Apply (PCA.32) to both running tables, retaining their alphabets,
partitions, starts, latches, entry map and reader halt labels.
Lemma 12.2 and induction give the same preparation state path on the
new $u$ as on the old $u^{\eta,L}$. Its latch is the literal original
$s(u)$ because that code is certificate-determined. After the supplied
handoff, the two reader entries are the same. The same induction gives
the reader state path on the new $u$ as on the old $u^{\eta,L}$.

The final halt retains its entire fixed row, which equals
$F(u^{\eta,L})=F(u)$ by NBP Theorem 10.4. Both call counts are equal
on this comparison and both literal sums weakly decrease, with each
forced constant query still paid. Thus every simultaneous upper bound
of the stated forms transfers on one actual origin. Sufficiency is
literal native installation of the two finite word tables on the
original full domain. No new code or entry is selected. $\square$

**Proposition 13.4 (why these scopes are different).**
Theorem 10.3's code-only basis justifies separate uniform phase bounds
with the reader fixed. It does not supply equality of an unchanged
reader's replies on $u$ and its padded comparison source. Theorem 13.1
adds exactly those finite reader observations before making a correlated
comparison. Theorem 13.3 changes the reader table under the separate
permission of Definition 13.2 and instead simulates both old phases
on one padded source.

Proof. A code certificate requires constancy of $c$, not constancy of
all reader observations. A frontier branch can be $E$ on one source
and a larger branch image on another. Their root replies agree while
their right-child replies are alpha and beta or branch, respectively.
Both are actual image values and can be put into an otherwise injective
all-image filling of the repeated-partner row by choosing the other
branch classes different from both. NBP's inverse gives actual sources.
Thus retaining a root observation alone does not retain that suffix
observation. The larger depth of Theorem 13.1 retains it; the changed
reply map of Theorem 13.3 simulates it on the selected padded source.
No failure of a particular coupling is asserted to refute every possible
smaller correlated basis. $\square$

## 14. The original executed-literal boundary and a finite actual-word task

**Theorem 14.1 (a total literal upper budget bounds semantic determination).**
Suppose an original preparer of Definition 2.2 succeeds on the entire
original fiber with total executed literal upper budget $\ell\in\mathbb N_0$.
Then the original code and complete entry are constant on equality
of all actual replies at absolute words of length at most $\ell$:

$$
\left(\forall v\in\mathcal W,\ |v|\le\ell\Rightarrow
 r_{\rho u}(v)=r_{\rho u'}(v)\right)
\ \Longrightarrow\ c(u)=c(u'),\quad s(u)=s(u').
\tag{PCA.35}
$$

No bound on the lengths of unused installed words is a hypothesis.
No such word is charged as if it had executed. The statement holds
with sourcewise termination in place of a separately specified call
upper bound.

Proof. On a successful run every visited literal has length at most
$\ell$, because its length is a nonnegative summand of that one run's
literal total. Follow the successful run on $u$. Its common start is
the start on $u'$. At every running visit, the visited word is within
the stated depth, so its reply agrees and the successor is identical.
Induction reaches the same latch on $u'$. Correctness and complete
entry recoverability give (PCA.35). No claim has been made about a
word in a state outside this run. The stationary no-revisit principle
also supplies a finite call bound from the finite alphabet if needed.
$\square$

**Definition 14.2 (finite original-word task at $(H,p,\ell)$).**
Let

$$
W_\ell=\{v\in\mathcal W:|v|\le\ell\}.
\tag{PCA.36}
$$

Use the actual finite profiles $\Omega_\ell$ of Definition 11.1.
Every original word in $W_\ell$ has a reply determined by such a
profile and the exterior: a hole suffix cannot be longer than its
absolute word. Assume the semantic constancy in (PCA.35), and assign
to each attained $W_\ell$ reply tuple its original complete entry.
Equivalently assign $s_\eta$ on $\Omega_\ell$, with equal $W_\ell$
reply tuples assigned the same entry. This assignment is supplied or
defined from the original code under the validity assertion; it is
not assumed computable uniformly from arbitrary program text.

On the prescribed installed preparation alphabet with $H$ states,
partition, common start and literal latches, choose one word of
$W_\ell$ for every running state and four successors. For each
$\eta\in\Omega_\ell$, require its induced path to end at the original
$\widehat{s_\eta}$, with at most $p$ running visits and sum of absolute
word lengths at most $\ell$. Every installed state counts; every
running visit costs one, including a root call of word length zero.
The fixed reader, including every whole-row halt label, remains exactly
as supplied. Neither this finite task nor its installed realization
provides a profile reader, chart decoder, source-dependent selector,
workspace, runtime address operation or silent visit.

**Theorem 14.3 (exact original-budget criterion).**
Original preparation with the fixed reader and original entry is
feasible at $H,p,\ell$ if and only if (PCA.35) holds and the finite
original-word task of Definition 14.2 is feasible at those same prices.
The assertion can also be made on an exact prescribed installed
alphabet, partition and common start, rather than only its cardinality.

Proof. Necessity of constancy is Theorem 14.1. In a feasible native
table, any state whose installed word is longer than $\ell$ is never
visited on any required actual source. Change the word in each such
state to $\varepsilon$, keeping its successors, partition, identity
and start. Every original required run is unchanged: by induction it
never reaches a changed state. Thus all installed words may be put
in $W_\ell$ without altering any required path or executed cost.
This operation neither charges unused long words nor removes their
counted states.

For words in $W_\ell$, each actual reply is determined by the finite
profile. Every retained profile is actually attained by Theorem 11.2;
hence the native table's correctness and prices give exactly the
finite task conditions. Conversely, install any task table literally.
Every original actual source has one retained profile, and induction
reproduces that profile's paid path and original complete entry.
The untouched reader then returns the whole predecessor row. $\square$

**Proposition 14.4 (zero budgets, graph structure and conditional finiteness).**
At $p=0$, feasibility means the fixed common start is already the
correct literal latch on the entire fiber. At $\ell=0$, running
visits are permitted but can submit only $\varepsilon$; its repeated
reply is stationary and each visit is charged. All other code
distinctions must fail (PCA.35). Empty cuts, a root cut and zero
classes need no additional convention beyond §§10–11.

For a supplied valid certificate, Definitions 12.3 and 14.2 give
finite mathematical table tasks with the original state identities,
actual word prices and complete latch labels. One can check a proposed
table on the finite attained response family, stopping any nonterminal
path at its first repeated running state. This is a finite table
criterion conditional on its literal code assignment. It is not a
uniform method for finding a determining certificate for arbitrary
acquired-term programs, even when finite preparability is promised.

Proof. The budget claims follow from the nonnegative execution
charges and the absence of silent running transitions. A repeated
running state on a fixed response tuple repeats its entire stationary
suffix forever, by Lemma 2.3, so it cannot be on a terminating path.
Different profiles can nevertheless traverse shared states differently;
cycles in the union of all four-successor edges and unused states are
permitted. Neither finite task imposes Bryant's variable ordering or
global acyclicity. The nonuniformity assertion is Theorem 15.2 below.
$\square$

## 15. No uniform extractor even under totality and finite-preparability promises

**Definition 15.1 (a compatible uniformly described code family).**
Use exactly the full repeated-partner fiber $\mathcal U_*$ of Definition
4.1 and the same fixed eight-state reader, two recoverable complete
entries $e_0,e_1$, and whole-row outputs of Supplier application 4.3.
A finite deterministic machine description $e$ has a prescribed initial
configuration; let $\tau_e\ge1$ be its first halting stage if it halts.
Stage one includes the check for an already halting initial configuration.
Let $h(B)$ be the maximum leaf depth of an acquired finite tree $B$.
For an acquired branch image define the total finite computation

$$
f_e(B)=
\begin{cases}
\mathbf1_{\{r_B(L^{\tau+1})=\mathsf{branch}\}},
 &\text{if the description halts first at stage }\tau\le h(B),\\
0,&\text{if it has not halted by stage }h(B).
\end{cases}
\qquad \sigma_e=\sigma_{f_e}\text{ of (PCA.12).}
\tag{PCA.37}
$$

The bounded simulation in this definition is a computation on the
already acquired finite term. It always ends; it requires no decision
of eventual halting. Heights, simulations and variable-length traversal
of an acquired term belong only to this code-specification computation,
with its supplied acquisition and separate costs. They are not operations
or uncounted workspace supplied to the paid stationary preparer or reader.
The complete paid-reader entry is always exactly $e_{\sigma_e(u)}$.

**Theorem 15.2 (promised finite preparation does not give a uniform extractor).**
Every program in (PCA.37) is total on acquired finite data and its original
code is finitely preparable on the entire $\mathcal U_*$. All share
precisely the same original eight-state, at-most-two-call reader of 4.3.
Nevertheless there is no effective procedure which, on every program
in this family, terminates and returns any one of the following:

1. a valid finite determining absolute depth for its original code;
2. a valid finite native determining menu for that code;
3. a finite installed stationary fixed-address common-start preparer
   generating its original complete entry on the entire fiber.

Thus no such extractor exists on all program descriptions under the
promises of totality and finite preparability. This does not obstruct
Theorems 10.3–14.3 with a supplied valid certificate.

Proof. If $e$ never halts, $f_e\equiv0$. If it halts at stage $\tau$,
then on every branch image

$$
f_e(B)=\mathbf1_{\{r_B(L^{\tau+1})=\mathsf{branch}\}}.
\tag{PCA.38}
$$

Indeed, if $h(B)\ge\tau$, the bounded simulation discovers that first
stage and uses exactly this test. If $h(B)<\tau$, a node at depth
$\tau+1$ cannot be a branch; the test and (PCA.37) are both zero.
Hence in the halting case this is one fixed finite suffix test, and
in the nonhalting case it is constant. In either case a finite menu
of class roots, together with $LLL L^{\tau+1}$ in the halting case,
determines the literal code on the entire fiber: roots identify the
profiles in (PCA.12), and the suffix decides its only varying case
$Z_{b_3}$. Theorem 3.2 supplies a finite preparer with the original
entries. This existence argument makes no uniform choice between the
two cases. Supplier application 4.3 serves every $f_e$ without any
change to the reader table, entries, outputs or two-call bound.

We next prove the required actual-source lower witness rather than
appeal to Rice's theorem. Suppose $e$ halts first at $\tau$ and set
$m=\tau+1$. Let $B^-$ be the complete all-beta tree with leaves at
depth $m$. Let $B^+$ replace its beta at occurrence $L^m$ by
$\langle\beta,\beta\rangle$. Both are finite branch images, because
beta and ordered pairs of images are images. They agree at every
relative word of length less than $m$, while

$$
r_{B^-}(L^m)=\beta,\qquad
r_{B^+}(L^m)=\mathsf{branch},\qquad
f_e(B^-)=0,\quad f_e(B^+)=1.
\tag{PCA.39}
$$

The last equations hold even if one evaluates via (PCA.37): both
heights are at least $m>\tau$. Choose four other finite branch images
for $c,b_1,b_2,b_4$, mutually distinct and avoiding both $B^-,B^+$.
Such choices exist by the infinite distinct image orbit used in NBP
Proposition 15.2. Set $x_{b_3}=\beta$, take $x_a=B^-$ or $B^+$,
and keep those four other values fixed. Each valuation has six
pairwise distinct values, all images. Its full current filling is
an image, repeats $a$ at both $LLL,LRL$ and $c$ at both $RLL,RRL$,
and has the exact original complete row. NBP Proposition 9.3 and
its inverse give two actual finite origins $u^-,u^+\in Z_{b_3}$,
with the same whole predecessor target $R_0$ and different prescribed
codes and complete entries.

Every absolute word of length less than $m+3=\tau+4$ has the same
reply on their current trees. Above the cut it sees the common
exterior. In every class other than $a$ the entire subtree is unchanged.
In either occurrence of $a$, its suffix length is less than $m$,
so (PCA.39)'s common prefix gives the same reply. This covers every
original address, including absent words in unchanged classes. Thus
any determining absolute depth $D$, or any determining menu whose
maximum word length is $D$, must satisfy

$$
D\ge\tau+4\quad\text{whenever }e\text{ halts at }\tau.
\tag{PCA.40}
$$

Now suppose an extractor in item 1 or 2 exists. From its returned
finite output obtain $D$ (use zero for an empty menu) and simulate
$e$ through stage $D$. If it halts, report halting. If it does not,
it cannot halt later: a later $\tau>D$ contradicts (PCA.40). This
would decide halting for arbitrary finite descriptions, although every
input supplied to the extractor is within its promised class.

For item 3, take the maximum length of all words in the returned
finite preparer's installed running states, again using zero for no
running states. Lemma 2.3 makes that installed menu determining, so
the same reduction applies. Unused long words may make this bound
larger; they remain finite and do not invalidate the halting decision.
They are used here only as a bound extracted from a finite description,
not charged as executions.

The undecidability endpoint is the standard halting problem. Alan M.
Turing's *On Computable Numbers, with an Application to the
Entscheidungsproblem*, §8, pp. 247–248, proves the corresponding absence
of a general procedure determining whether an arbitrary described
machine ever prints a specified symbol. The equivalence needed here
is explicit: simulate any machine until its first halt and then print
a distinguished symbol; conversely simulate a printing machine until
its first occurrence of that symbol and then halt. Both transformations
are effective finite descriptions. A bounded simulation at a returned
$D$ is a finite operation, so the supposed extractor contradicts this
endpoint. No premise about partiality of the code programs, failure of
the finite-preparability promise, or additional source port is used.
$\square$

## 16. Supplier scope, comparison and realization assumptions

**Assumption 16.1 (resource interpretation and operational premises).**
The resources in §§10–15 are the exact installed preparation and reader
state alphabets, actual running visits and sums of submitted absolute
word lengths. Every running, latch and whole-output state counts,
including unused installed states. A terminal latch has no native call;
every running visit has one, including a forced constant reply or
$\varepsilon$. Handoff and the phase boundary are the separately
supplied operations of Definition 2.2. No phase coordinate is silently
added to a running configuration. If an implementation requires phase,
entry or service storage, that storage has its own price under the
supplied realization contract; the theorems do not construct it.

Literal table substitution can change the stored literals and successors
of the preparation graph, and in Theorem 13.3 also of the design-variable
reader graph. The state identities, partitions, starts, latch contents,
complete recoverable entry values and whole-row halt labels are as
stated in each theorem. Installed-address representation, all four
successor slots, output representation, acquisition, acquired-term
computation, authentication, export, isolation, entry, local work,
elapsed time, energy and native service retain separate prices. Their
costs are not determined by state/call/submitted-word counts.

**Proposition 16.2 (mathematical suppliers and the additional bridge).**
The supplier roles in the preceding deductions are the following.

| Supplier | Used statement and exact scope |
| --- | --- |
| [NBP, Definitions 1.1–1.2, 10.1 and (NBP.10.3)][NBP] | Original finite ordered trees, complete canonical row, all legal injective class valuations and the bijection to actual origins by the image inverse. These retain repetitions and entire class disequalities. |
| [NBP, Proposition 10.2 and Theorem 10.4][NBP] | Branch subtrees of an image are images; exact exterior image parsing; class-root determination of the entire predecessor row. The target remains that row throughout. |
| [LRD, Theorem 2.2][LRD] | One finite simultaneous assignment with prescribed intrinsic rank one, arbitrarily deep leaves and every syntactically nontrivial whole-term negative. Theorem 11.2 applies this supplier after the literal prefix decomposition; it does not claim a new general filling theorem. |
| [Signed Local Prefix Lifting, Lemma 2.1][SLP] | The related general live-prefix and simultaneous-negative supplier, with fixed finite barriers and shared names. The present image-specific bridge uses LRD's rank-one specialization directly; it never applies unrestricted prefix lifting without checking image membership or a live frontier. |
| [Native Ambient Contact Decision, Theorem 6.1 and Definition 1.2][NAC] | Total joint-prefix decision for its explicit exact-cover grammar and signed finite-source conditions. It does not decide arbitrary acquired-term programs or supply a determining certificate for them. |
| [NBP, Proposition 12.5, Definitions 13.1 and 14.2][NBP] | Stationary no-revisit, shortest repeated occurrence, submitted literal sums, counted common start and terminal latch. The proofs retain paid visits instead of using silent forced-successor contraction. |
| [NBP, Theorem 14.4 and Proposition 15.8][NBP] | The earlier jointly reselected-encoder bridge and the failure of universal arbitrary-code padding. A supplied finite determining certificate is the added hypothesis here; none of these arguments pads an arbitrary prescribed code without it. |
| [NBP, Theorem 15.5 and PCA 4.3][NBP] | The very same eight-state reader serving every code in (PCA.12), including the entire program family (PCA.37), without changing its complete entries. |
| [Prescribed binary codes: a nine-state escape, Theorems 4.1, 5.1 and 6.1][NRE] | The actual $E$-sensitive suffix distinction, nine-state two-call reader and exclusion of every same-code root-only two-call reader. A certificate-relative basis may include that suffix; no root-only claim for arbitrary code horizons is made here. |

Proof. Theorem 11.2 substitutes typed image residuals into the original
legal-row map and uses LRD on exactly its full negative list. Lemma
12.2 then identifies every finite competitor word with one actual
basis word and an installed reply map on the selected actual origins.
Theorem 10.3 uses that identity without altering the reader;
Theorems 13.1 and 13.3 respectively preserve reader observations or
redesign its graph. These are the additional paid, original-entry
correspondences. Theorem 15.2 adds the actual whole-fiber embedding
needed for its halting reduction. The cited suppliers alone do not
assert these fixed-code arbitrary-budget conclusions. $\square$

**Proposition 16.3 (classical comparisons and evidence boundary).**
Finite-prefix dependence is classical. Magnus Steinby, Eija Jurvanen
and Antonio Cano, *Varieties of Unranked Tree Languages*,
[arXiv:1510.07402v1, §10.2][SJC], define $k$-definite languages by
membership constant on equal $k$-root segments, with early finite
leaves retained. This is the relevant background for the semantic
notion, not a source of the native resource bounds. Their trees are
unranked and their language definition includes recognizability;
the present domain is the specific fixed-arity actual inverse fiber,
with four native replies and no assumed recognizer for arbitrary
code-program text. Inclusive depth conventions can differ by one.

Randal E. Bryant, *Graph-Based Algorithms for Boolean Function
Manipulation*, [§2, Definition 1][BRY], requires increasing variable
indices on each nonterminal edge, hence an acyclic ordered function
graph. The finite tasks here allow four replies, repeated words at
different states, unused states, state sharing and cycles in the union
graph. They preserve the original entry and the actual paid literal
at each state. Consequently no BDD node count, minimization claim or
Boolean numerical frontier is transferred. The finite task is not
an uncharged profile-reading interface.

Turing's [§8][TUR] supplies only the undecidability endpoint in
Theorem 15.2, whose promise-preserving native reduction is proved
there. The repository's [Rice background note][RICE] does not by
itself prove that promised-total, promised-finitely-preparable
extraction is impossible. No graph, XOR, quantum or spectral numerical
bound is a premise for the correspondence.

Proof. The stated classical definitions have the described domains
and do not mention the original native entry, image inverse, complete
row partition or execution prices. The exact parameter correspondence
and missing implications are those stated above. The deductions in
§§10–15 are repository-derived ordinary-paper mathematics relative
to their attributed suppliers. They carry no claim of current Lean
kernel verification or worldwide priority. A finite certificate and
a finite abstract table establish the stated mathematical feasibility
under Assumption 16.1; they do not establish acquisition, authentication,
export, isolation, entry or physical finite-control service realization.
The general continuing relational-fiber goal includes those residual
operational obligations. $\square$

[LRD]: RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_LITERAL_ROOT_DEPTH.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[NAC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_AMBIENT_CONTACT_DECISION.md
[NRE]: FIB_PRESCRIBED_CODE_NINE_STATE_ROOT_ESCAPE.md
[SJC]: https://arxiv.org/html/1510.07402v1#S10.SS2
[BRY]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[TUR]: https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf
[RICE]: ../../../Library/Diagonal/rice1953classes.md

## 追加锚（本行以下为增补区）

## 17. Sparse selected addresses with the original complete entries

**Definition 17.1 (total selected-address descriptions).** Retain the
entire original $\mathcal U_*$, its six injective class values, both
occurrences of $a,c$, the eleven profiles and the five complete canonical
rows of Definition 4.1. Retain exactly the code template (PCA.12) and
the one fixed reader of Supplier application 4.3. In particular its
alphabet consists of three running states and five whole-row halts,
its two distinct complete entries are the same $e_0,e_1$, and its
table, entry map and complete halt outputs are immutable. Its separate
upper budgets remain $K=8,q_R\le2,\ell_R\le6$.

Let $a:\mathbb N_{\ge1}\to\{0,1\}$ be a specified total computable
predicate, with no known support bound. Set

$$
\begin{aligned}
A&=\{s\ge1:a(s)=1\},& w_s&=L^sR,\\
f_a(B)&=\bigvee_{1\le s\le h(B)}
 \bigl(a(s)=1\ \land\ r_B(w_s)=\mathsf{branch}\bigr),&
\sigma_a&=\sigma_{f_a}\text{ of (PCA.12)}.
\end{aligned}
\tag{PCA.41}
$$

Here $h(B)$ is maximum leaf depth and an empty disjunction is false.
The argument $B$ is an acquired finite branch image. This specifies a
total computation on acquired data: only finitely many evaluations of
the total $a$ are needed on each input. There is no uniform bound on
their work or on input height. A branch reply at $w_s$ implies
$h(B)\ge s+2$, so the height cutoff removes no true disjunct.
Equivalently, $f_a$ tests whether any selected $w_s$ has branch reply;
alpha, beta and absence are all false. This equivalence holds for
arbitrary branch images, including shapes other than combs.

Only this predicate and the resulting prescribed code vary with $a$.
The cut, current row, source fiber, target, native words and replies,
reader and its original complete entries do not vary. The computation
in (PCA.41) specifies the code; it is not a runtime operation available
to a preparer. In particular it supplies neither a height register nor
an address operation, simulation workspace or copy of the acquired term.

**Convention 17.2 (the preparation design and its budgets).** Use exactly
Definition 2.2. For the basic state count there are precisely the two
installed latches $\widehat e_0,\widehat e_1$ and a finite set $V$ of
running states. A prescribed common start is a member of $V$. The
installed literals and all four successors may be designed; state
identities, the running/latch partition, start and literal latch contents
can be fixed in advance. An upper state budget $H$ permits a choice of
such an alphabet with at most $H$ members. Every installed state counts,
including unused ones; every running visit costs one actual call,
including forced replies and the root word $\varepsilon$. Its literal
charge is the sum of the lengths of the submitted absolute words.
There are no silent running transitions. A start already fixed to a
latch cannot generate these codes, since both values occur on positive
profiles. Additional mandated latches are addressed in Theorem 19.1.

## 18. Exact actual supports for sparse selection

**Lemma 18.1 (finite inverse origins with exact six-address supports).**
For any finite nonempty $S\subseteq A$, there are actual finite origins
$u_0,(u_s)_{s\in S}\in Z_{b_3}$, all with whole target $R_0$, such that
$\sigma_a(u_0)=0$, $\sigma_a(u_s)=1$, and the exact set of differing
current replies on the pair $(u_0,u_s)$ is

$$
E_s=\{p w_s v:p\in\{LLL,LRL\},\quad
                         v\in\{\varepsilon,L,R\}\}.
\tag{PCA.42}
$$

The sets $E_s$ are pairwise disjoint. Every word of $E_s$ has absolute
length at least $s+4$. All other finite addresses, including every
deeper absent continuation, have identical replies on that pair.

Proof. Put $G=\langle\beta,\beta\rangle$, $C_0=G$, and
$C_{m+1}=\langle C_m,\beta\rangle$. Choose $m\ge\max S$.
Take $B_0=C_m$ and let $B_s$ replace the beta at $w_s$ by $G$.
The words $w_s$ are prefix-free. In $B_0$ every $w_t$, $t\ge1$,
has beta or absent reply. In $B_s$ exactly $w_s$ among these words
has branch reply. All these trees are finite branch images, since beta
and pairs of images are images. They are pairwise distinct, and
(PCA.41) gives $f_a(B_0)=0,f_a(B_s)=1$.

Choose four pairwise distinct branch images $D_c,D_1,D_2,D_4$ avoiding
all the finitely many $B$ values. The infinite supply is NBP Proposition
15.2. Set $x_a=B_0$ or $B_s$, $x_{b_3}=\beta$, and
$x_c=D_c,x_{b_j}=D_j$ for $j=1,2,4$. Each tuple has six pairwise
distinct values, all images. NBP Proposition 9.3 gives the actual finite
origin $u=\delta(\mathscr S(x))$, with $\rho u=\mathscr S(x)$,
current row exactly $R_*$ and predecessor row exactly $R_0$.
Both occurrences of $a$ contain the same chosen $B$ and both occurrences
of $c$ contain $D_c$; none of the class disequalities is dropped.

Inside $B_0,B_s$ the tested node $w_s$ changes from beta to branch.
At $w_sL,w_sR$ the replies change from absent to beta. At every
strict descendant of either child both replies are absent. Proper
prefixes of $w_s$ remain branches, and every disjoint subtree is
unchanged. Thus the relative difference set is exactly
$\{w_s,w_sL,w_sR\}$, including the tested node itself.
Above the depth-three cut both currents have the same branch skeleton.
Any longer word has a unique cut prefix. In an unchanged class its
whole reply function is unchanged; in either $a$ occurrence the actual
occurrence identity (NBP.9.7) gives precisely the relative comparison
just proved. This proves (PCA.42) for every actual finite address and
all four possible replies, rather than just for the tested menu.
Prefix-freeness and disjoint occurrence cones prove disjointness and
the length bound. $\square$

**Lemma 18.2 (an additional paid distinction on the same negative run).**
On the source $u_0$ of Lemma 18.1, every successful preparer makes at
least one call outside $\bigcup_{s\in S}E_s$ whose word has length at
least three. This call can be forced in addition to one distinguishing
call for each $s\in S$.

Proof. Keep $x_a=B_0$ and $x_{b_j}=D_j$ for $j=1,2,4$, but change
$x_c=D_c$ to beta and $x_{b_3}=\beta$ to alpha. This is an injective
tuple in the positive alternative $3$ of NBP Proposition 9.3; its actual
finite inverse $u_+$ belongs to $\Pi_3$ and requires entry $e_1$.
The source $u_0$ requires $e_0$. Their currents differ only in the
two $c$ occurrence cones and the $b_3$ cone. Any differing reply
therefore has length at least three and lies outside every $E_s$.
If all queries on the terminating $u_0$ path had equal replies on
$u_+$, induction from the common start would give the same latch,
a contradiction. The same path argument against each $u_s$ forces
a query in $E_s$. These are distinctions on one actual execution,
not costs added from different maximizing sources. $\square$

## 19. The exact simultaneous three-resource frontier

**Theorem 19.1 (sparse prescribed-code preparation spectrum).** If $A$
is finite, set $n=|A|$ and $W=\sum_{s\in A}(s+4)$, with $n=W=0$
for the empty set. Under Convention 17.2 the complete preparation
upper-budget region on the entire original $\mathcal U_*$ is exactly

$$
\boxed{\quad H\ge n+4,\qquad
 p\ge\max(2,n+1),\qquad
 \ell\ge\max(6,3+W).\quad}
\tag{PCA.43}
$$

One table attains all three coordinate minima simultaneously, with
the original code, literal entries and unchanged eight-state reader.
On an alphabet fixed in advance with exactly two latches, this table
can be installed whenever $|V|\ge n+2$ and the prescribed start is
running; surplus running states remain installed and counted. If $r$
additional distinct latches are mandated, the exact state threshold is
$n+4+r$, with at least $n+2$ running states and a running start still
necessary and sufficient. The other two minima are unchanged.

If $A$ is infinite, no finite installed preparer generates this code
on the entire original fiber, even under sourcewise termination alone.

Proof, upper bound. List finite $A$ as $s_1<\cdots<s_n$. Install the
two original-entry latches and running states $D,T,A_1,\ldots,A_n$.
The common start is $D$. In the table below $A_{n+1}$ means
$\widehat e_0$; when $n=0$, the beta successor of $D$ is also
$\widehat e_0$.

| Running state | Absolute literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | $A_1$ if $n>0$, else $\widehat e_0$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |
| $A_i$ | $LLL L^{s_i}R$ | $A_{i+1}$ | $A_{i+1}$ | $\widehat e_1$ | $A_{i+1}$ |

The last row is used for $1\le i\le n$. Each $A_i$ is a distinct
installed state with one literal address, not a loop index or runtime
counter. An alpha at $b_3$ is exactly $\Pi_3$ and requires one.
A beta at $b_3$ is exactly $Z_{b_3}$; the chain computes the exact
disjunction (PCA.41), using actual absence and both leaf replies as
false. If $b_3$ is branch, the only remaining code-one profile is
$\Pi_4$, detected by alpha at $b_4$. This verifies all four positive
and all seven zero profiles. In particular it imposes no comb shape
or other restriction on the branch fillings. All four successors are
installed even where a reply at a class root is unattained.

There are $n+2$ running states and two latches. The two possible longest
paths have costs $(2,6)$ and $(n+1,3+W)$; for $n=0$ the beta path
has only $(1,3)$. When $n>0$, the negative comb source of Lemma 18.1
with $S=A$ follows $D,A_1,\ldots,A_n$, attaining the second path's
costs. A $Z_c$ source follows $D,T$, attaining $(2,6)$.
For $n>0$ one has $n+1\ge2$ and $3+W\ge8>6$, so both execution
maxima occur on the comb source; for $n=0$ both occur on the $Z_c$
source. Extra running states or mandated latches can be made
unreachable with arbitrary total successor assignments and remain
counted. Relabel $D$ as the prescribed running start. No source-dependent
choice of tables or start occurs at execution.

Proof, lower bounds for finite $A$. First let $n>0$ and take $S=A$
in Lemma 18.1. Different required latches force the terminating $u_0$
path to query a word in every $E_s$. Otherwise equal replies along
that path force the same latch on $u_s$. Disjointness forces $n$
different visits of total literal charge at least $W$. Lemma 18.2
forces one more visit of length at least three on this same path.
Thus $p\ge n+1$ and $\ell\ge3+W$, regardless of how many states
or other resources are allowed.

For the baseline two-call and six-letter bounds use the same actual
$Z_c$ source and its two replacements from Lemma 7.1. Replacing only
$b_3$ or only $b_4$ by alpha gives respectively $\Pi_3$ and $\Pi_4$,
both requiring code one instead of zero. On the zero-source path there
must be a distinguishing query in each of these disjoint occurrence
cones. Each has absolute length at least three. Hence $p\ge2$ and
$\ell\ge6$ for every $A$, including the empty set.

Every $E_s$ also requires an installed running word there, by the
same path argument. Lemma 7.1 already supplies mandatory installed
words in the $b_3$ and $b_4$ cones for every code of (PCA.12).
Those cones and all $E_s$ are disjoint, so $|V|\ge n+2$.
Both original entries are attained on positive profiles, requiring
both distinct original-entry latches. All extra mandated latches
also count. This proves the state bound, including $n=0$.
It applies to arbitrary shared four-successor graphs, with cycles,
unused states and repeated literal words allowed. A forced or root
call cannot eliminate a required distinction: every word outside
the stated difference support has equal replies on its comparison
pair and is still a paid visit.

Proof, infinite $A$. A finite installed menu has a finite maximum
absolute word length $d$. Choose $s\in A$ with $s+4>d$ and use
Lemma 18.1 with $S=\{s\}$ and $m=s$. Its negative comb has no
branch at any $w_t$, including every other selected position, and
its replacement has a branch at exactly $w_s$. Thus their prescribed
codes differ even for infinite $A$. Every word of their exact difference
support is longer than $d$. The two actual sources agree on the entire
installed menu, forcing identical paths and latches by Lemma 2.3.
If that path fails to terminate, correctness already fails. This
contradiction needs no advance uniform call bound. $\square$

**Corollary 19.2 (cardinality and weight as distinct preparation data).**
For this family finite preparability is equivalent to finite support of
$a$. Among finite supports of the same cardinality the state and call
minima coincide, whereas the literal minimum depends on the sum of
the selected indices. The parameters are not the number of leaves
of a full context: unselected side leaves of the comb are not tested
by the code. For any $s$ selected alone the exact vector is
$(5,2,s+7)$, and for the empty support it is $(4,2,6)$.

Proof. These are substitutions into (PCA.43); the infinite case is the
last part of Theorem 19.1. The proof of that theorem supplies the
full-domain upper and the all-address actual-source lower that make
these substitutions legitimate. $\square$

## 20. Total descriptions and the effective preparation boundary

**Definition 20.1 (promise and ambient meanings of an index).** In a
fixed effective programming system let $\mathsf{Tot}_2$ consist of
descriptions computing a Boolean value at every positive integer.
For an input promised to lie in $\mathsf{Tot}_2$, use exactly (PCA.41).
Outside that promise a computation of $a(s)$ can diverge, and the
prescribed acquired-term computation need not be total. No conclusion
below treats those ambient descriptions as promised inputs.

A promise semidecision terminates on the designated side of the
promise and never gives that answer on the other promised side;
its behavior outside the promise is unrestricted. For ordinary
arithmetical index labels we use the following explicit total syntax.
Fix an effective numbering of finite enumerator descriptions, and let
$W_{e,t}$ be the finite set emitted during its first $t$ transition
steps, with $W_{e,0}=\varnothing$. Define

$$
b_e(s)=\mathbf1_{\{W_{e,s}\setminus W_{e,s-1}\ne\varnothing\}},
\qquad \Gamma(e)=\mathsf{Sparse}(\underline e).
\tag{PCA.44}
$$

The canonical numeral $\underline e$ occurs literally in this syntax.
Its prescribed evaluator on $B$ is (PCA.41) with $a=b_e$: structural
height computation followed by simulations bounded by that height.
The admitted strings of this particular sublanguage are exactly
$\{\mathsf{Sparse}(\underline e):e\in\mathbb N\}$, with canonical
numerals, so membership and recovery of $e$ are decidable. There is no
claim that arbitrary syntactically valid programs are total or that
this sublanguage represents every total code. Each of these particular
strings is total by its explicit bounded evaluator. All static program
parameters are common data, not source-dependent control fields.

**Theorem 20.2 (a total-description finite-preparability classification).**
On the promise $\mathsf{Tot}_2$, finite preparation of $\sigma_a$ is
exactly finite support of $a$. It has neither a positive nor a negative
uniform semidecision on that promise. On the explicit total syntax
(PCA.44), the set

$$
\{e:\sigma_{b_e}\text{ has a finite original-entry preparer on }
                          \mathcal U_*\}
\tag{PCA.45}
$$

is $\Sigma^0_2$-complete under computable many-one reductions.
Every input to those reductions describes a total acquired-term code
served by precisely the unchanged reader of 4.3. Its resource vector,
when finite, is the exact vector of Theorem 19.1, with $A$ the stages
of genuinely new enumeration events and $W$ their weighted sum.

Proof. The source-specific equivalence is Corollary 19.2.
An enumerator emits only finitely many distinct numbers if and only
if only finitely many stages introduce a new number. Hence (PCA.45)
is the classical finite-c.e.-set index problem $\mathsf{FIN}$.
For this explicit syntax its upper definition is
$\exists N\,\forall s>N\, b_e(s)=0$, with a decidable bounded-simulation
matrix. Totality is built into (PCA.44), rather than inserted as an
extra quantifier over arbitrary program indices.

For completeness, the standard $\mathsf{FIN}$ reduction can be made
explicit. Given any predicate $\exists m\forall n\,R(z,m,n)$ with
decidable $R$, at stage $t$ let

$$
c_t=\min\bigl(\{m\le t:\forall n\le t\ R(z,m,n)\}
                                     \cup\{t+1\}\bigr).
\tag{PCA.46}
$$

Construct an enumerator that successively computes and emits $c_t$.
Each stage ends because $R$ is decidable; a finite enumerator description
is effectively obtained from $z$. The sequence $c_t$ is nondecreasing:
an excluded old candidate never returns, and the only newly eligible
candidate at the next stage is the previous default. If a least true
witness $m$ exists, it is eventually the least remaining candidate and
$c_t=m$ thereafter. If none exists, every fixed finite set of candidates
is eventually excluded, so $c_t$ is unbounded. The emitted set is
therefore finite exactly for the stated $\Sigma^0_2$ predicate.
Its transition-step enumeration need not share the stage numbers $t$;
finiteness is unchanged by that finite effective simulation.

Neither semidecision assertion needs a hierarchy-separation assumption.
For an arbitrary machine $e$, the total predicate that is one exactly
while $e$ has not halted by stage $s$ has finite support exactly when
$e$ halts. The total predicate that is one exactly when $e$ has halted
by stage $s$ has finite support exactly when $e$ never halts. These
are uniform bounded simulations and preserve the totality promise.
A negative semidecision in the first reduction or a positive one in
the second would semidecide nonhalting. Together with the usual halting
semidecision that would decide halting, contradicting Turing's endpoint.
This proves both assertions. $\square$

**Theorem 20.3 (validity and all-three-budget feasibility remain different
from supply).** For a promised total $a$, invalidity of a proposed finite
menu certificate with literal entry labels is semidecidable. So is
failure of feasibility at a supplied triple $H,p,\ell$ for this sparse
family. Neither corresponding positive property is decidable, even
with both totality and finite preparability promised. On syntax
(PCA.44), each is $\Pi^0_1$-complete: for certificate validity this
already holds for one fixed proposed certificate, and for budget
feasibility for any fixed triple with $H\ge4,p\ge2,\ell\ge6$.
Triples failing one of those baseline inequalities are uniformly
infeasible and are excluded from that hardness assertion.

Proof. A certificate is a finite menu $M$ and a finite assignment
$\chi$ of its reply tuples to the original $e_0,e_1$, with arbitrary
completion on unattained tuples. Enumerate finite origins, retain
exactly those with $R_P(\rho u)=R_*$, and evaluate the promised total
code and actual finite replies. A mismatch with $\chi$ refutes validity.
It is found after finite work whenever one exists. If just menu
determination is proposed, enumerate pairs instead and look for
equal menu replies with unequal codes. The class test is exact finite
tree computation; no regular-language assumption on the whole fiber
is being used. These are mathematical semidecision constructions,
not additional operations supplied to a native running state.

For budgets satisfying the baseline, Theorem 19.1 makes feasibility
equivalent to the simultaneous inequalities

$$
|A|\le H-4,\qquad |A|\le p-1,\qquad
\sum_{s\in A}(s+4)\le\ell-3.
\tag{PCA.47}
$$

If $A$ is infinite these finite thresholds all eventually fail.
Successive evaluations of the total $a(s)$ semidecide a violation
of any one inequality, and every violation has a finite witness.
For (PCA.44) this gives an ordinary co-c.e. property of all $e$;
equivalently every finite partial count and weight obey their bounds.
The same applies to validity, since every described evaluator is total.

For hardness, let $M_0$ be the six representative class roots and
let $\chi_0$ return $e_1$ if $b_3$ or $b_4$ has alpha reply,
and $e_0$ otherwise. This is a valid certificate for $A=\varnothing$.
It is invalid for every nonempty singleton support: Lemma 18.1 gives
same-root actual sources in $Z_{b_3}$ with different required entries,
and $\chi_0$ assigns zero to both.

Given an arbitrary machine $e$ and a fixed feasible baseline triple,
construct an enumerator which first takes more than $\ell+1$ dummy
transition steps, then simulates $e$, and emits just one number if
and when $e$ first halts. No other number is ever emitted. Its compiled
description is effective and its emitted set is always finite. Apply
$\Gamma$ to that description. The selected support is empty if $e$
never halts, and otherwise is a singleton $\{s\}$ with $s>\ell+1$.
In the latter case the exact literal minimum $s+7$ exceeds $\ell$.
Thus both validity of $(M_0,\chi_0)$ and feasibility at the given
triple hold exactly when $e$ never halts. Every reduced input is total
and finitely preparable, with the same source, code template and fixed
reader. Nonhalting is the classical co-c.e.-complete endpoint; bounded
simulation and the explicit native frontier establish the required
promise-preserving reductions. $\square$

**Remark 20.4 (index scope and distinct tasks).** The $\Sigma^0_2$ and
$\Pi^0_1$ statements concern the explicit total presentation (PCA.44).
For arbitrary program numbering, totality is an additional ambient
index property. No such arithmetical label for the conjunction of
totality and preparation is asserted here. The promise results are
strong because the reductions actually land in the promise, not
because off-promise descriptions were treated as total.

Validity of a supplied certificate, extraction of some valid certificate,
decision of a given three-budget request, construction of a mathematical
table from valid finite data, and actual realization with paid services
are separate questions. Theorem 15.2 already excludes a uniform extractor
under totality and finite-preparability promises; that extraction theorem
is reused without a second proof. Theorems 12.4 and 14.3 already give
the exact finite mathematical table tasks once the entry assignment
and determining facts are supplied. The new resource inequalities
(PCA.43) and (PCA.47) expose cardinality and address weight for an
unbounded family, rather than inferring those prices from mere
termination of the input computation.

## 21. An explicit native interface to the existing certificate supplier

**Definition 21.1 (additional effective regular description).** Suppose
a finite total deterministic bottom-up tree automaton $\mathfrak A_f$
is supplied. Write its leaf states as $q_\alpha,q_\beta$, its binary
transition as $\delta_f$, and its accepting set as $F_f$; thus
$q_f(\alpha)=q_\alpha$, $q_f(\beta)=q_\beta$ and
$q_f(\langle B,C\rangle)=\delta_f(q_f(B),q_f(C))$.
Require the exact specification

$$
\forall B\in\mathcal I\text{ with branch root},\qquad
 f(B)=1\ \Longleftrightarrow\ q_f(B)\in F_f.
\tag{PCA.48}
$$

Its ranked signature is exactly $\alpha:0,\beta:0,\langle-,-\rangle:2$.
The code is still the prescribed $\sigma_f$ of (PCA.12), with the same
entries and immutable reader. The explicit automaton and equivalence
are extra finite-description input. Existence of some equivalent
regular language, or totality of an arbitrary acquired-term program,
does not supply them or decide their equivalence to that program.

Use one coordinate for each of the six whole class values, not eight
independent hole values. Write $\mathcal B_I$ for branch images and
let $\mathcal D(x)$ be the conjunction of all different-class
disequalities with the following disjunction of eleven coordinate
conditions:

$$
\begin{aligned}
Z_* &: \quad \bigwedge_d x_d\in\mathcal B_I,\\
Z_d &: \quad x_d=\beta\ \land\!
                       \bigwedge_{k\ne d}x_k\in\mathcal B_I,\\
\Pi_j &: \quad x_{b_j}=\alpha\ \land\ x_{\operatorname{partner}(j)}=\beta
 \ \land\!
 \bigwedge_{k\notin\{b_j,\operatorname{partner}(j)\}}
                                      x_k\in\mathcal B_I.
\end{aligned}
\tag{PCA.49}
$$

Here $d$ ranges over the six classes and $j=1,\ldots,4$, with
partner $a$ for $j=1,2$ and $c$ for $j=3,4$.
NBP Propositions 9.3 and 15.2 identify this domain exactly with the
entire original fiber by $x\mapsto\delta(\mathscr S(x))$.
On it define the Boolean expression

$$
\widehat\sigma_f(x)=
 \Pi_3(x)\lor\Pi_4(x)\lor
 \bigl(Z_{b_3}(x)\land[q_f(x_a)\in F_f]\bigr),
\tag{PCA.50}
$$

and on two tuples retain the complete joint bad-pair relation

$$
\mathcal D(x)\land\mathcal D(y)\land
       \bigl(\widehat\sigma_f(x)\mathbin{\mathsf{xor}}
                                  \widehat\sigma_f(y)\bigr).
\tag{PCA.51}
$$

**Supplier application 21.2 (ARH productive-prefix saturation with native
entry fidelity).** Under (PCA.48), the existing productive-prefix test
of [ARH, Lemma 21.4][ARH] decides whether $\sigma_f$ has a finite
original-entry preparer on the whole $\mathcal U_*$, and supplies a
valid finite determining menu and its literal entry labels in the
positive case. In the negative case it supplies actual finite origin
pairs with different prescribed entries and identical current replies
through any requested finite absolute depth. Consequently the existing
finite tasks of Theorems 12.4 and 14.3 decide every given three-budget
request on these explicitly described inputs and construct a finite
mathematical table when feasible. None of these automata is installed
as a free runtime instrument.

Proof. The image grammar $\mathcal I::=\beta\mid E\mid
\langle\mathcal I,\mathcal I\rangle$ is a finite regular tree grammar.
Intersecting it with branch-root type gives $\mathcal B_I$.
Ground equality, root type and a supplied automaton's coordinate
acceptance are effective coordinate predicates. Equality of two whole
coordinates, and its negation, use the padded synchronous convolution
of ARH Lemma 21.1, taking decoration powers zero. That lemma also
supplies lifting to larger tuples with correct padding, Boolean
operations, prefix restrictions and finite witnesses. Combining it
with the ordinary finite-tree automaton closures gives an effective
automaton for (PCA.51) on twelve coordinates. It retains the full
$\mathcal D$ separately in both copies, every one of its disequalities,
and the single shared value for each repeated class. This is not a
product relaxation of the native domain.

Apply ARH Lemma 21.4 directly to this bad-pair automaton. Its productive
state initialization, descending diagonal-prefix sets, effective
stabilization and finite accepting witnesses are the existing supplier;
no new pair-state saturation algorithm is needed. Its proof and
statement use the automaton, productive states and diagonal labels,
so the instantiation requires exactly the bad relation just constructed.
For some finite $h$, the positive answer excludes bad pairs whose
corresponding class replies agree at every relative word of length
less than $h$. By the original occurrence identity, such tuple agreement
is exactly current-tree agreement at all absolute words of length
less than $h+3$: all shorter exterior words are fixed, and each longer
word enters its unique cut occurrence. Every class has a depth-three
representative. Thus the actual menu

$$
M_h=\{p_dw:d\text{ a class},\ |w|<h\},\qquad
\max_{v\in M_h}|v|\le h+2\quad(h>0)
\tag{PCA.52}
$$

determines the original entry. For each attained tuple of replies,
intersect $\mathcal D$ with its finite coordinate-prefix conditions
and extract a finite witness by ARH Lemma 21.1. Evaluate (PCA.50)
on that witness and assign the literal original $e_0$ or $e_1$.
Absence of Bad proves independence of the witness. Unattained tuples
can receive either existing entry. If $h=0$ the menu is empty and
the same argument requires a constant code; the present template's
two positive code values rule that case out on the nonempty domain.

If the stable accepting intersection is nonempty, ARH Lemma 21.4
supplies a finite bad tuple pair with arbitrarily long diagonal
prefix. Apply it, for example, at $h=d+1$ for a requested absolute
depth $d$. The occurrence identity gives identical current replies
at every $|v|\le d$. Both tuples satisfy $\mathcal D$, so their
filled currents have the actual finite inverses
$u=\delta(\mathscr S(x)),u'=\delta(\mathscr S(y))$. Equation (PCA.48)
and (PCA.50) make their original prescribed entries different.
These are actual sources with all sharing and disequalities intact,
not infinite limit objects. Theorem 3.2 excludes a finite preparer.

In the positive case the supplied menu and assignment are exactly the
inputs of Theorem 12.4. Its finite attained actual-word task can be
checked over finitely many tables on a specified finite alphabet;
stationary path checks stop at a latch or the first repeated running
state, as Proposition 14.4 states. The same reasoning applies under
state upper budget $H$ with the two mandated latches and a running
start. Feasible tables retain the literal entries and use genuine
absolute native words with the original state, call and literal charges.
The reader and all five of its whole-row halt outputs remain unchanged.
Theorem 14.3 supplies its separate executed-literal formulation.
These are applications of the existing synthesis tasks, not new
generic finite-search results. $\square$

**Remark 21.3 (the exact supplier boundary).** ARH Theorem 22.1 already
owns its constructor-elimination complete-row criterion, finite
stabilization consumer and finite bad-source witnesses. Its eligibility
grammar and full-row target are not silently enlarged to arbitrary
code programs here. Application 21.2 uses its Lemma 21.4 at the explicit
automaton interface, with (PCA.49)–(PCA.51) providing the native domain,
code-disagreement and original-entry correspondence. No unknown chart
selector is needed in this single six-class presentation.

The repeated-class set of filled current trees is not asserted to be
an ordinary regular tree language: copying the same coordinate at two
different holes retains a global equality condition. Regularity is
used on padded tuples of the six coordinates and their two-copy
comparison. [NRF, Definitions 1.3–1.5 and Proposition 9.1][NRF] keeps
its public finite automaton selector and constrained original-source
presentation; [NAC, Definition 1.2][NAC] keeps its exact-cover
mixed-template language. Neither supplier
automatically admits an arbitrary additional code predicate. For a
general total program the missing positive interface is precisely an
explicit applicable finite description and its exact equivalence to
the prescribed function. Semantic existence does not fill that gap.

## 22. Attribution, mathematical scope and separately priced realization

**Convention 22.1 (sources of the deductions).** NBP Proposition 9.3,
its occurrence identity (NBP.9.7), Proposition 15.2 and Theorem 15.5
supply respectively the actual inverse origins and complete rows,
every-address reading, the exhaustive eleven profiles with infinitely
many distinct branch images, and the one fixed eight-state reader.
The image parser is [Transport–Memory Completion, Proposition 22.2,
(RA.2207)][TMC]. Definitions 2.2 and 4.2 fix the preparation mechanics
and code throughout. Lemma 7.1 supplies the two mandatory right-class
cones; Theorem 3.2 supplies the semantic finite-menu criterion.
Theorems 12.4, 14.3 and 15.2 retain ownership of certificate-relative
synthesis, the executed-literal finite task and promised non-extraction.

The additional source-specific deductions are the exact supports
(PCA.42), the sparse cardinality/weight frontier (PCA.43), its
promise-preserving total-description consumers and the explicit
native tuple/entry application (PCA.49)–(PCA.52). Unlike a full-context
slot code, a sparse selection omits arbitrarily many side slots and
also admits infinite support. Its all-address lower proof and
full-domain matching table are needed to obtain the exact resource
and effective conclusions. These are repository-derived ordinary
paper deductions, not a worldwide novelty or current kernel claim.

Finite-tree automata determinization, Boolean closure and effective
emptiness are classical: Joost Engelfriet, *Tree Automata and Tree
Grammars*, Theorems 3.8, 3.32 and 3.74 in the
[author-uploaded text][ENG]. They concern finite ranked trees.
ARH Lemmas 21.1 and 21.4 supply the specialized padded-convolution
and productive diagonal-prefix constructions used here. Their
algorithms are not reintroduced as new theorems. Theorem 20.2 gives
the standard finite-c.e.-set completeness reduction explicitly;
the arithmetical level is classical computability terminology.
Turing's [§8, pp. 247–248][TUR] supplies the undecidability endpoint
for occurrence of a distinguished printed symbol. Simulation until
first halt followed by printing, or simulation until first such print
followed by halting, gives the effective correspondence to halting
used here. Nonhalting is co-c.e.-complete since a semidecision of
the complement of any co-c.e. set can be made to halt exactly on
that complement. Rice's general index theorem is not used to
replace any native support or promise-preservation proof.

**Assumption 22.2 (operational and price boundary).** Acquisition of
the row and acquired code arguments, authentication of the same
origin/version and update, pre-cut query permission, actual export,
complete isolation, faithful code-only handoff, lawful reader entry,
stationarity and native service remain supplied and separately priced.
The preparation and reader phases have exactly the alphabets,
partitions, starts and latch/output labels specified above. Every
installed running, terminal latch and whole-output state counts;
every actual running visit is paid, including root and forced calls.
All length sums are submitted absolute literal lengths, with no
amortization across phases. Handoff, phase/service storage, address
representation, installed tables, output representation and acquired-term
computation keep their separate prices. The three coordinates
$H,p,\ell$ are not total physical memory, energy or elapsed time.

There is no source-dependent hidden selector, surviving archive or
code reread, computed address, extra counter or phase coordinate,
copied specimen, free observation, runtime automaton or uncharged
decoder. A finite abstract table and a mathematical synthesis procedure
do not construct those services or their physical realization.
The nine-state prescribed-code escape and its separate root-call
results concern a different reader contract. Continuous-control,
quantum and trace-log suppliers likewise require their own proved
source, action, legality and resource correspondences before any
native preparation conclusion could be transferred. None is used
as a numerical or physical preparation transfer here.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[TMC]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[ENG]: https://arxiv.org/pdf/1510.02036
[NRF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_REGULAR_FRONTIER_SELECTION.md

## 追加锚（本行以下为增补区）
