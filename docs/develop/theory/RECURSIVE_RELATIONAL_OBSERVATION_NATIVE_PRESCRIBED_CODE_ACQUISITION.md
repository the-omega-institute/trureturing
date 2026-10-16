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

## 23. Second-hit acquisition with the original prescribed entries

**Definition 23.1 (finite selected thresholds).** Fix a supplied finite
set $A=\{s_1<\cdots<s_n\}$ of distinct positive integers, $n\ge3$.
Write $w_i=L^{s_i}R$ and

$$
W_A=\sum_{i=1}^n(s_i+4),\qquad
f_{A,k}(B)=\mathbf1_{\{\sum_{i=1}^n
                 \mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}\ge k\}},
\qquad \sigma_{A,k}=\sigma_{f_{A,k}},\quad 1\le k\le n.
\tag{PCA.53}
$$

Both leaf replies and absence contribute zero. Each formula specifies
one new acquired-term function and hence one prescribed code on every
member of the original $\mathcal U_*$. It is defined even when $B$
has none of the selected comb shape. The second-hit code is
$\sigma_{A,2}$; the near-unanimity code is $\sigma_{A,n-1}$.
The other values of $k$ provide the common lower and construction
lemmas consumed by these two cases.

Retain Definitions 1.1, 4.1 and 4.2 literally: finite nonempty ordered
alpha/beta trees, the same homomorphic $\rho$, the whole unbounded
one-image fiber, the two occurrences of each repeated partner, and
all six-class disequalities. The code remains zero on $\Pi_1,\Pi_2$,
one on $\Pi_3,\Pi_4$, the value (PCA.53) on $Z_{b_3}$, and zero on
all other zero profiles. It is not a recoloring of an already
prescribed input. In particular the near-unanimity case does not
complement the code on the other profiles.

**Convention 23.2 (unchanged reader and all allowed preparers).** Keep
exactly Supplier application 4.3's eight installed reader states,
its two original complete entries $e_0,e_1$, entry map, four-successor
reader table and five whole-row halts. Handoff must install precisely
$e_{\sigma_{A,k}(u)}$. The reader's separate upper budgets remain
$K=8,q_R\le2,\ell_R\le6$. Its output $R_0$ is the complete original
row $R_*$. Each $R_j$, $1\le j\le4$, is exactly NBP Proposition
9.3's row: replace the two holes at $q_jL,q_jR$ by a concrete beta
at $q_j$, retain every other exterior part and old hole, restrict the
whole equality partition, and recompute its canonical names. All
remaining disequalities and strict-prefix blocking guards are retained.
The other occurrence of the repeated partner is still an old hole.
These literal complete outputs are supplied, not reconstructed from a
root-type answer in the preparation phase.

Preparation uses Definition 2.2 and Convention 17.2 with a common
running start. Competitors are all finite stationary fixed-literal
four-successor shared graphs accurate on the entire $\mathcal U_*$.
Only sourcewise termination is required initially. Repeated words at
different states, shared successors, cyclic union graphs and unused
states are admitted. Every installed state and every running visit is
charged; a constant reply, absence or a root query is not free. Initially
there are the two original-entry latches. If $r$ further distinct
latches are mandated, all $r$ are also installed and counted. No bound
on tree size, height or interior shape is imposed on the upper domain.

## 24. A simultaneous actual cube and the meaning of every address

**Lemma 24.1 (actual selected-bit realizations).** There is a family of
actual finite origins $(u_\theta)_{\theta\in\{0,1\}^n}\subset Z_{b_3}$
with whole predecessor row $R_0$ and

$$
\sigma_{A,k}(u_\theta)=\mathbf1_{\{\sum_i\theta_i\ge k\}}.
\tag{PCA.54}
$$

For every actual finite word $v$, its reply on this family is either
constant or depends injectively on exactly one coordinate $\theta_i$.
The latter case occurs precisely at

$$
E_i=\{p w_i z:p\in\{LLL,LRL\},\ z\in\{\varepsilon,L,R\}\}.
\tag{PCA.55}
$$

These sets are disjoint. At $p w_i$ the two replies, in bit order
$0,1$, are $(\beta,\mathsf{branch})$; at its two children they are
$(\mathsf{absent},\beta)$. Every word in $E_i$ has length at least
$s_i+4$. There is no address reading a combination of two bits.

Proof. Reuse the finite comb construction of Lemma 18.1, now making
all selected replacements simultaneously. Explicitly let
$G=\langle\beta,\beta\rangle$, $C_0=G$ and
$C_{m+1}=\langle C_m,\beta\rangle$, with $m\ge s_n$.
In $C_m$, independently replace the beta at $w_i$ by $G$ exactly
when $\theta_i=1$; call the result $B_\theta$. Prefix-freeness of the
$w_i$ makes this a well-defined finite branch image. Distinct bit
vectors give different trees, since their selected root replies differ.
Choose four pairwise distinct branch images $D_c,D_1,D_2,D_4$ avoiding
all these finitely many trees, using NBP Proposition 15.2's infinite
branch-image supply. For every $\theta$ set

$$
x_a=B_\theta,\quad x_{b_3}=\beta,\quad
x_c=D_c,\quad x_{b_j}=D_j\quad(j=1,2,4),\qquad
u_\theta=\delta(\mathscr S(x)).
\tag{PCA.56}
$$

All six values are pairwise distinct images. NBP Proposition 9.3
therefore supplies an actual finite inverse with exactly the original
current row and whole predecessor row $R_0$. Both occurrences of $a$
use the same $B_\theta$ and both occurrences of $c$ use $D_c$.
The selected replies give (PCA.54) directly from the prescribed code.

At a selected relative root the replacement changes beta to branch,
and at its two children changes absent to beta. Below either child
both replies are absent. Proper prefixes remain branch, disjoint
subtrees are unchanged, and the selected cones are disjoint. These
statements hold simultaneously for every selected replacement.
A word shorter than three stays in the fixed exterior. Every longer
word has one cut prefix; an unchanged class gives a constant reply,
while either $a$ occurrence reduces to its actual suffix in
$B_\theta$ by (NBP.9.7). This proves the complete address classification
(PCA.55), including both leaf labels, absence, unselected slots and
arbitrarily deep words. No observational restriction has been placed
on a competitor. The finite family is used only for lower bounds;
its inverse and bit coordinates are proof objects, not runtime ports.
$\square$

**Lemma 24.2 (three singly installed bits cannot decide the interior
threshold).** Fix $2\le k\le n-1$ and any preparer correct on the
whole original domain. Let $m_i$ be the number of its installed
running states whose literal belongs to $E_i$. Then

$$
m_i\ge1\quad(1\le i\le n),\qquad
\bigl|\{i:m_i=1\}\bigr|\le2,\qquad
\sum_i m_i\ge2n-2.
\tag{PCA.57}
$$

Proof. On the actual family of Lemma 24.1, each installed state is
analytically either a test of one bit or a fixed-successor state.
At a bit test its two successors are those for the two actual replies
in Lemma 24.1. The other reply edges are irrelevant to this lower
comparison. All four native edges remain part of the original table.
For each $i$, fix $k-1$ of the other bits to one and all remaining
bits to zero. Changing bit $i$ changes the prescribed code. Without
an installed word in $E_i$ every menu reply would agree, contradicting
Lemma 2.3 and the different required latches. Hence $m_i\ge1$.

Suppose three indices each had exactly one such installed state.
Fix precisely $k-2$ of the other $n-3$ bits to one, and the rest to
zero; this is possible throughout the stated interior range. The
remaining prescribed predicate is two-of-three on the three unfixed
bits. Every other installed state now has a fixed successor on this
restricted family. For the following impossibility argument only,
suppress paths through these fixed-successor states. Such suppression
is a mathematical examination of state paths, not a free native
transition offered to a preparer, and it is not used to reduce any
execution charge.

This leaves at most three test vertices, one for each unfixed bit,
a common start, and the two possible terminal values. Suppression is
well-defined on reachable edges: a reachable unique bit has not been
tested before on the prefix reaching its vertex, so either of its
values can extend that prefix. A fixed-successor infinite path after
such an edge would give a nonterminating actual input. The same
argument applies to the initial fixed-successor path. Terminal values
are identified here solely for the impossibility argument; the
original literal latches are not identified in the installed apparatus.

The reachable three-test graph must be acyclic. A simple path to a
first vertex of a directed cycle has no vertex of that cycle earlier
on it. All tested bits on that prefix and on one traversal of the
cycle are distinct. Assign them the values selecting those edges.
This is a consistent assignment that reaches and repeats the cycle,
contradicting sourcewise termination. Thus acyclicity is proved only
for this unique-bit restriction, not assumed for the competitor's
union graph.

There cannot be an acyclic three-test graph for two-of-three. Let its
first test be $x$, leaving $y,z$. Its zero continuation must compute
$y\land z$, and its one continuation must compute $y\lor z$.
Both nonconstant residuals depend on both remaining variables, so each
continuation must start at $y$ or $z$ and must have a path testing both.
If the two continuations start at the same vertex they are the same
residual function, a contradiction. If they start at different vertices,
one requires a path from $y$ to $z$ and the other a path from $z$ to
$y$, contradicting acyclicity. This excludes the three singleton
indices. With at most two $m_i$ equal to one and all others at least
two, summation gives $\sum_i m_i\ge2n-2$. Repeated tests, unreachable
states and cycles elsewhere in the installed graph have not been
excluded or counted as separate path copies. $\square$

## 25. Lower bounds with unrestricted repeated-read competitors

**Theorem 25.1 (interior-threshold installed-state bound).** For every
$2\le k\le n-1$, every accurate finite preparer in Convention 23.2
has

$$
|V|\ge2n,\qquad H\ge2n+2+r.
\tag{PCA.58}
$$

The bound is independent of any larger finite call or literal budget.

Proof. Lemma 24.2 counts at least $2n-2$ installed running states
at words in the disjoint $E_i$. Lemma 7.1 applies to every code of
the unchanged template (PCA.12): there must also be an installed
running word in the $b_3$ occurrence cone and another in the $b_4$
occurrence cone. Those cones are disjoint from all $E_i$ and from
each other. These are two further states, regardless of how much
sharing occurs on executions. Both prescribed values occur on the
positive profiles, so the two distinct literal-entry latches are
necessary. Adding every mandated further latch proves (PCA.58).
The argument neither unrolls the graph nor imposes a read-once or
ordered competitor. $\square$

**Theorem 25.2 (call and absolute-literal lower bounds).** For every
$1\le k\le n$, every successful finite preparer has an actual source
$u\in Z_{b_3}$ on whose one preparation execution

$$
q_P(u)\ge n+1,\qquad
\ell_P(u)\ge3+W_A.
\tag{PCA.59}
$$

Consequently these are independent lower bounds on uniform upper
budgets, even when arbitrarily many finite installed states are allowed.

Proof. Examine the actual cube (PCA.56). Keep a partial assignment of
its bits only in this proof. At the first query in $E_i$, assign that
previously unassigned bit one if fewer than $k-1$ distinct bits have
already been assigned one; otherwise assign it zero. Reply with the
actual value prescribed by Lemma 24.1. Later queries in $E_i$ use
the same bit. Every query outside the union has the constant actual
reply on the cube. Thus every finite response prefix is realized by
all completions of its current partial assignment.

After $d<n$ distinct bits have been queried, the counts of assigned
ones and zeros are $\min(d,k-1)$ and $\max(0,d-k+1)$. There are
both zero-output and one-output completions: the assigned ones are
at most $k-1$, the assigned zeros are at most $n-k$, and at least
one bit is unassigned. A correct path therefore cannot yet latch.
Nor can it repeat a running state. At a first repeated state every
bit queried on the intervening loop is already assigned, so any
completion of the partial assignment would realize that deterministic
loop forever, contrary to sourcewise termination. Since the installed
alphabet is finite, these responses must reach all $n$ distinct bits.
Their completed vector $\theta$ has exactly $k-1$ ones. Subsequent
execution is the terminating run on the actual $u_\theta$, and its
required code is zero. In particular this one run contains a visit
in each $E_i$, charging at least $n$ calls and $W_A$ letters.

There is one further paid distinction on this same run. In (PCA.56)
keep $x_a=B_\theta$ and $x_{b_j}=D_j$, $j=1,2,4$, but replace
$x_c$ by beta and $x_{b_3}$ by alpha. The six values are still
pairwise distinct and satisfy positive alternative $3$ of NBP
Proposition 9.3. Its actual finite inverse $u_+$ is in $\Pi_3$ and
requires code one. Its current tree differs from $t_{u_\theta}$ only
in the $c$ occurrences and the $b_3$ occurrence. Equal replies along
the entire $u_\theta$ path would force the same latch on $u_+$.
A differing query on that path must therefore enter one of those
class cones. It has absolute length at least three and is outside
every $E_i$. Adding this different visit proves both bounds in
(PCA.59). No costs from different maximizing sources are added.
The adaptive bit choices establish existence of one actual source;
there is no adversary, counter or partial-assignment register in the
preparer's operational contract. $\square$

## 26. A whole-fiber threshold table with no auxiliary work state

**Theorem 26.1 (full-domain construction and its charged resources).**
For every $1\le k\le n$, a preparer for the prescribed $\sigma_{A,k}$
on the entire original $\mathcal U_*$ has

$$
H=k(n-k+1)+4+r,\qquad
p=n+1,\qquad \ell=3+W_A.
\tag{PCA.60}
$$

These are attained uniform call and literal maxima for this table,
not only loose upper bounds. The reader, both literal entries and
whole-row outputs remain those of Convention 23.2.

Proof. Install the two original-entry latches, running states $D,T$,
and a distinct running state $Q_{h,m}$ for every pair

$$
0\le h\le k-1,\qquad 0\le m\le n-k.
\tag{PCA.61}
$$

Each such pair has $h+m\le n-1$. In the following table let

$$
U^+_{h,m}=\begin{cases}
\widehat e_1,&h=k-1,\\
Q_{h+1,m},&h<k-1,
\end{cases}
\qquad
U^-_{h,m}=\begin{cases}
\widehat e_0,&m=n-k,\\
Q_{h,m+1},&m<n-k.
\end{cases}
\tag{PCA.62}
$$

The symbols in (PCA.62) are fixed successor names in a finite
installed table. They are not functions evaluated during execution.
Start at $D$ and install all four successors as follows.

| Running state | Absolute literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | $Q_{0,0}$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |
| $Q_{h,m}$ | $LLL L^{s_{h+m+1}}R$ | $U^-_{h,m}$ | $U^-_{h,m}$ | $U^+_{h,m}$ | $U^-_{h,m}$ |

There are $k(n-k+1)$ grid states. Their subscripts name separately
installed states and their displayed words are installed literals.
The only changing configuration is the current counted state;
there is no additional hit counter, miss counter, cursor, address
calculation, phase coordinate or saved source. Every transition out
of a running state is preceded by its one paid native invocation.
Any $r$ mandated further latches are unreachable and still count.

Check the full eleven-profile partition, not just the lower family.
Alpha at $b_3$ is exactly $\Pi_3$ and latches one. Beta there is
exactly $Z_{b_3}$ and enters the grid. By the occurrence identity,
its actual selected reply at $LLLw_i$ is $r_{x_a}(w_i)$ even when
the selected node is absent. The grid state $Q_{h,m}$ means only
that the first $h+m$ selected tests have produced $h$ branch replies
and $m$ other replies. This invariant is proved by induction on that
actual run; it is not an accessible second register. A branch makes
the $k$th hit exactly when $h=k-1$. A false test makes
$n-k+1$ false replies exactly when $m=n-k$, leaving fewer than
$k$ possible hits. Otherwise the next separately installed state
queries the next literal. Thus every branch image, of arbitrary
size and shape, receives exactly its value (PCA.53).

If $b_3$ is branch, the only remaining code-one profile is $\Pi_4$,
detected by alpha at $b_4$ in state $T$. All other profiles on this
path latch zero. This verifies every $\Pi_j$, every $Z_d$ and $Z_*$.
The absent successor at a class root is installed although that root
is reached throughout this domain. All other false replies in the
grid, including alpha and absent, have their specified zero-test
meaning. No native word or reply has been deleted from the apparatus.

On the grid path, $h+m$ increases at every step, so at most $n$
selected calls occur, each at most once in the fixed order. Including
$D$ gives at most $n+1$ calls and $3+W_A$ letters. The other path
has at most two calls and six letters. Since $n\ge3$ and each
$s_i\ge1$, the grid bounds dominate these other-path bounds.
For equality choose the actual cube vector with its first $k-1$
bits one and all remaining bits zero. The grid cannot reach either
terminal condition before the $n$th selected test, and then latches
zero. This one actual source attains both maxima. Counting the two
root-test states and all latches gives (PCA.60). $\square$

## 27. Exact second-hit frontier and the unbounded state premium

**Theorem 27.1 (exact entire preparation upper-budget region).** For
$\sigma_{A,2}$ with $n\ge3$, under Convention 23.2 the exact region is

$$
\boxed{\ H\ge2n+2+r,\qquad p\ge n+1,\qquad
                         \ell\ge3+\sum_{s\in A}(s+4)\ }.
\tag{PCA.63}
$$

One full-fiber table attains all three coordinate minima. With no
extra mandated latches $r=0$, this gives exactly the stated
$2n+2,n+1,3+W_A$ triple. On an alphabet fixed in advance with the
two original-entry latches and $r$ mandated further latches, a running
start and at least $2n$ running states are necessary and sufficient
for the minimum execution budgets. Every surplus installed state
is still counted. The same exact region holds for the separately
specified $\sigma_{A,n-1}$.

Proof. Theorem 25.1 applies to both interior thresholds and yields
$H\ge2n+2+r$, without restricting calls, literals, graph sharing or
repeated reads. Theorem 25.2 gives the other two necessary bounds
independently of the installed-state budget. For $k=2$ and for
$k=n-1$, the grid count in Theorem 26.1 is
$k(n-k+1)=2n-2$. Its one table therefore attains all three lower
bounds simultaneously on the entire domain with literal original
entries. Relabel its start $D$ as any prescribed running start.
Additional running states can be left unreachable with arbitrary
total four-successor tables and remain counted. A start fixed to a
latch cannot produce both attained codes. These facts prove both
sufficiency for upper budgets and the fixed-alphabet assertion.
For $n=3$ the two displayed predicates coincide; for larger $n$ the
two different predicates each have this proof. $\square$

**Corollary 27.2 (an arbitrarily large installed-state premium at
unchanged execution minima).** Compare the new $\sigma_{A,2}$ with
the existing finite sparse OR code $\sigma_a$ of Definition 17.1
for $a(s)=\mathbf1_{\{s\in A\}}$, under the identical original
reader, entry, source and preparation conventions. Their respective
minimum installed preparation cardinalities differ by exactly

$$
(2n+2+r)-(n+4+r)=n-2,
\tag{PCA.64}
$$

while their independent minimum call and absolute-literal upper
budgets are the same $n+1$ and $3+W_A$. The premium is unbounded
as the supplied finite set grows. It survives arbitrarily large
finite execution budgets.

Proof. Use the exact sparse OR frontier of Theorem 19.1 and the
second-hit frontier of Theorem 27.1. The lower state bound for each
holds with unrestricted larger finite execution budgets, and both
frontiers have a simultaneous attaining table. No encoder or reader
has been changed while solving either fixed input: this comparison
is between two explicitly different prescribed-code problems.
Both lower cubes have the same whole predecessor row $R_0$; the
extra state demand is for faithful original-code acquisition rather
than for distinguishing new predecessor outputs. $\square$

**Corollary 27.3 (the precise general-threshold conclusions used by
the endpoint cases).** For every $1\le k\le n$, the independent
minimum uniform call budget is $n+1$ and the independent minimum
absolute-literal budget is $3+W_A$. One table attains both at
$H=k(n-k+1)+4+r$. For every $2\le k\le n-1$, if $H_{\min}(A,k;r)$
denotes the minimum installed cardinality with no execution-budget
restriction, then

$$
2n+2+r\ \le\ H_{\min}(A,k;r)\ \le\ k(n-k+1)+4+r.
\tag{PCA.65}
$$

Proof. Theorem 25.2 and Theorem 26.1 give the two independent
execution minima. Theorem 25.1 and the same construction give
(PCA.65). These are the common bounds whose coincident endpoints
are consumed in Theorem 27.1. No equality for other interior $k$,
ordered-optimum transfer, or entire three-budget characterization
for those other thresholds follows from these bounds. In particular
the construction attaining both execution minima has not been
proved to have minimum installed cardinality for general $k$.
$\square$

## 28. Suppliers, comparison with branching programs and realization scope

**Attribution 28.1 (ordinary mathematical suppliers and added bridge).**
The dependency and permission correspondences are as follows.

| Supplier | Exact use and retained boundary |
| --- | --- |
| NBP Proposition 9.3, (NBP.9.7), Proposition 15.2 and Theorem 15.5; PCA Definitions 1.1, 4.1 and 4.2 and Supplier application 4.3 | Actual finite inverse origins, complete current and five predecessor rows, every-address occurrence reading, full eleven-profile partition, infinitely many distinct branch images, and the same eight-state reader with its original complete entries. The inverse and profile partition supply mathematical meaning, not extra runtime ports. |
| NBP Proposition 12.5 and PCA Lemmas 2.3 and 7.1 | Stationary per-source no-revisit, menu consistency, and the two mandatory disjoint right-class query cones. Cyclic union graphs remain allowed. |
| PCA Lemma 18.1 and Theorem 19.1 | The finite beta/pair comb and its exact local reply supports, and the already established sparse OR costs used in (PCA.64). Lemma 24.1 extends that support argument to the simultaneously varying actual cube needed for a threshold state lower bound. |
| PCA Theorems 3.2, 10.3, 12.4 and 14.3 | Existing finite determination, certificate-relative same-state recoding and paid finite-word synthesis. They do not evaluate the unrestricted threshold optimum. The new consumer is (PCA.63) and its premium (PCA.64), proved with the actual-address cube, singleton-state obstruction and full-fiber table. |
| NBP Theorems 12.4, 13.2 and 14.4 | Existing shared Moore and joint preparation/reader correspondences when their encoding permissions hold. Their freely chosen coloring is not substituted for the prescribed $\sigma_{A,k}$. |
| Nine-state root normalization, Theorem 7.1; table-driven common root normalization, Theorems 6.3 and 7.1 | Same-code reader normalization under their separate reader hypotheses. A good-entry set does not supply which literal entry the acquired code prescribes. These results neither generate (PCA.53) nor pay its preparation costs. |

The threshold grid is the classical success/failure construction for
symmetric Boolean functions. Wegener, *The Complexity of Boolean
Functions*, [Chapter 14, pp. 414–426][WBP], defines branching programs
as directed acyclic graphs in §14.1, Definitions 1.1–1.2. His
§14.4, Theorem 4.1 gives an ordered synchronous optimum specifically
for read-once programs on symmetric functions; Theorem 4.3 counts
their nonconstant residual vectors. Those results support the
construction comparison, not an unrestricted native lower bound.
Bryant's [§2, Definition 1][BRY] likewise requires strictly increasing
variable indices along edges. Neither hypothesis is imposed on the
competitors here. The three-singleton restriction argument in Lemma
24.2 proves exactly the weaker structural property needed for the
state lower bound without exporting either ordered or read-once
optimality to an unrestricted graph. Generic threshold-query or
branching-program constructions are not claimed as new mathematics.

Sinha and Thathachar, *Efficient Oblivious Branching Programs for
Threshold and Mod Functions*, [DOI 10.1006/jcss.1997.1530][STBP], is
a comparison lead for the distinction between oblivious and read-once
restrictions. No numerical bound or theorem from that paper is a
premise of (PCA.57)–(PCA.65). The native conclusions here are
repository-derived ordinary paper deductions with the supplier map
above, without a worldwide originality or current kernel claim.

**Boundary 28.2 (which services and prices remain supplied).** Keep
Assumptions 1.2 and 22.2 throughout. Acquisition and authentication of
the complete current row and acquired code arguments, the same
origin/version and update, lawful pre-cut access, actual export,
complete isolation, code-only handoff, faithful original reader entry,
stationarity and the native service are supplied and separately priced.
The constructions price every installed preparation running and latch
state; the separate reader prices all its running and whole-output
states. Every running visit costs one native invocation, including
constants and the root. Submitted literal charges are absolute lengths,
without a relative-address cursor or cross-phase amortization.

Installed table representation, all four successors, literal address
storage, the two entry contents, whole-output storage, initialization,
handoff and service/phase storage, transitions and local acquired-term
computation retain their separate prices. No total physical storage,
physical time or energy optimum is asserted by $H,p,\ell$. Grid
labels and the lower-proof bit assignments are not extra accessible
running coordinates. There is no free selector, surviving archive,
source copy, address operation, work register, counter, decoder or
later code reread.

Promised interleaved word recovery and common calibration-budget
results have different acquisition and input promises. The known-Schur
channel capacity contract supplies independent uses of a fixed known
channel and allows block encoding; native critical-cutoff limits concern
specified continuous forms, sources and clocks. None supplies the
same-source native operation, legality, update or price map needed
to transfer a numerical resource to this preparer. Quantum carrier and
continuous-control dimensions are not installed native state counts.
No such transfer is used here. The unchanged reader still outputs the
whole original predecessor row, while the new theorem concerns how
the prescribed literal reader entry is acquired before that reading.

[WBP]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[STBP]: https://doi.org/10.1006/jcss.1997.1530

## 追加锚（本行以下为增补区）

## 29. Two paid scans for the same prescribed threshold entry

**Definition 29.1 (unchanged native task and static notation).** Fix
exactly the supplied $A=\{s_1<\cdots<s_n\}$, $n\ge3$, and
$1\le k\le n$ of Definition 23.1. Throughout §§29–33 the function
being prepared is literally $\sigma_{A,k}$ of (PCA.53) and (PCA.12),
on the entire original unbounded $\mathcal U_*$. Retain the source
algebra, update, actual inverse origins, complete current row and
all five complete canonical predecessor rows of Definitions 1.1 and
4.1 and Convention 23.2. In particular both occurrences of $a$ and
both of $c$, every distinct-class disequality and every strict-prefix
blocking guard are retained. The finite cube of Lemma 24.1 is not
an upper-domain promise. Every original finite address remains legal,
and all four native replies remain in the interface; the finite installed
menu does not restrict that address universe.

The reader remains Supplier application 4.3's fixed eight-state
reader with its original complete entries $e_0,e_1$, entry map,
three running states and five literal whole-row halts. Preparation
must latch exactly $\widehat e_{\sigma_{A,k}(u)}$; the paid handoff
enters exactly that complete original entry. The reader's separate
bounds remain $K=8$, $q_R\le2$, $\ell_R\le6$. Neither its code
nor its entries nor any of its four successors are design variables.

For notation in finite tables put

$$
\chi(\mathsf{branch})=1,\qquad
\chi(\alpha)=\chi(\beta)=\chi(\mathsf{absent})=0,
\qquad a_i=LLLw_i=LLL L^{s_i}R.
\tag{PCA.66}
$$

Thus $|a_i|=s_i+4$ and $\sum_i|a_i|=W_A$. Writing an edge
using $\chi$ means installing its four specified successors; it
provides no extra reply operation. On any actual filling the native
occurrence identity gives $r_{t_u}(a_i)=r_{x_a}(w_i)$, including
absence and continuations blocked by either leaf. For a branch image
$B$, write $h(B)=\sum_i\chi(r_B(w_i))$ only as a mathematical
quantity used in proofs. No acquired value, bit vector or value of
$h(B)$ is an accessible preparation argument.

**Theorem 29.2 (explicit repeated-query resource point).** Under the
unchanged permissions and prices of Definition 29.1 and Convention
23.2, every supplied $A$ and $k$ have a finite common-start preparer
on all of $\mathcal U_*$ with

$$
\boxed{\ H=n(2\lceil\sqrt n\rceil+1)+4+r,\qquad
p=2n+1,\qquad \ell=3+2W_A.\ }
\tag{PCA.67}
$$

The displayed call and literal costs are the attained uniform maxima
of this one construction, and $H$ is its exact installed cardinality,
including every unreachable state and all $r$ mandated further
latches. The only mutable preparation configuration is its current
counted state.

Proof. The two modular scans below are a native use of the classical
modular-router and two-box exact-division method: see Sinha's
[dissertation, Proposition 3.10, Definitions 3.14 and 3.17, and the
exact-division attribution on printed p. 42][SINHA95]. The modular
method is a credited supplier; the present assertion specifies and
prices its original-entry native consumer.

Let

$$
d=\lceil\sqrt n\rceil,\qquad e=d+1,\qquad
c=(-k)\bmod d\in\{0,\ldots,d-1\},\qquad J=(k+c)/d.
\tag{PCA.68}
$$

Here $J$ is an integer with $1\le J\le d$, since
$1\le k\le n\le d^2$. Every $0\le h\le n$ satisfies

$$
0\le h+c\le d^2+d-1<de.
\tag{PCA.69}
$$

Install distinct running states $D,T$ and, independently, all states

$$
U_{i,j}\quad(1\le i\le n, 0\le j<d),\qquad
V_{i,z}\quad(1\le i\le n, 0\le z<e).
\tag{PCA.70}
$$

Install the two original-entry latches and the $r$ mandated further
latches. All states in (PCA.70) count even when they are unreachable
from the common start. A modular remainder in the following formulas
always names a fixed member of its displayed finite range.

For $\varepsilon\in\{0,1\}$ define the following *table entries*,
with $j'=(j+\varepsilon)\bmod d$ and
$z'=(z+\varepsilon)\bmod e$:

$$
\begin{aligned}
F_U(i,j,\varepsilon)&=
\begin{cases}
U_{i+1,j'},&i<n,\\
V_{1,(c-j')\bmod e},&i=n,
\end{cases}\\
F_V(i,z,\varepsilon)&=
\begin{cases}
V_{i+1,z'},&i<n,\\
\widehat e_1,&i=n\text{ and }(-z')\bmod e\ge J,\\
\widehat e_0,&i=n\text{ and }(-z')\bmod e<J.
\end{cases}
\end{aligned}
\tag{PCA.71}
$$

Start at $D$. Install precisely the following literals and all four
successors at every running state.

| Running state | Absolute literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | $U_{1,c}$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |
| $U_{i,j}$ | $a_i$ | $F_U(i,j,0)$ | $F_U(i,j,0)$ | $F_U(i,j,1)$ | $F_U(i,j,0)$ |
| $V_{i,z}$ | $a_i$ | $F_V(i,z,0)$ | $F_V(i,z,0)$ | $F_V(i,z,1)$ | $F_V(i,z,0)$ |

Formulas (PCA.68)–(PCA.71) describe source-independent choices of
literal successor names at installation. In particular the final
comparison, modular remainders and first-to-second-scan connection
are already reflected in those names. Execution has no modular
arithmetic instruction, decoder, phase register, bit register,
cursor, source copy, computed address, reset or silent connection
step. The symbols $i,j,z$ distinguish separately installed states;
there is no mutable tuple alongside the one current state. The
$r$ further latches are installed but unreachable.

First examine an arbitrary $u\in Z_{b_3}$, with arbitrary finite
branch image $x_a=B$. The paid $D$ query returns beta. Put
$\theta_i=\chi(r_B(w_i))$ and $h=\sum_i\theta_i$ only for this
proof. Induction on the first scan shows that its state before
reading $a_i$ is $U_{i,(c+\sum_{v<i}\theta_v)\bmod d}$. Thus its
last paid edge selects the second scan's first state with residue
$(c-j_*)\bmod e$, where $j_*=(h+c)\bmod d$.

Each repeated query is on the same stationary current tree. It
therefore has the same $\theta_i$ in the second scan, whatever the
shape of $B$. Induction on that scan shows that its residue after
its last reply is

$$
z_*=(c-j_*+h)\bmod e
    =d\left\lfloor\frac{h+c}{d}\right\rfloor\bmod e.
\tag{PCA.72}
$$

By (PCA.69), $v=\lfloor(h+c)/d\rfloor$ lies in
$\{0,\ldots,e-1\}$. Since $d\equiv-1\pmod e$, (PCA.72)
implies $(-z_*)\bmod e=v$. Consequently the installed final edge
latches one exactly when

$$
v\ge J
\quad\Longleftrightarrow\quad h+c\ge dJ=k+c
\quad\Longleftrightarrow\quad h\ge k.
\tag{PCA.73}
$$

This is exactly the prescribed code on $Z_{b_3}$. The proof used no
comb shape, bound on tree size or distributional assumption. Both
leaf labels and absent replies have been handled by the installed
zero successors, not removed from the native alphabet.

For completeness check all other members of the eleven-profile
partition of Definition 4.1. Alpha at $b_3$ occurs exactly on
$\Pi_3$ and selects $\widehat e_1$. Beta occurs exactly on
$Z_{b_3}$, already proved. On the remaining branch-at-$b_3$
profiles, alpha at $b_4$ occurs exactly on $\Pi_4$ and selects
$\widehat e_1$ from $T$. Every other such profile, including
$\Pi_1,\Pi_2$, every other $Z_d$ and $Z_*$, selects
$\widehat e_0$. Class-root absence cannot occur on this complete
cut but its successors are installed. Thus every actual finite
origin in $\mathcal U_*$ reaches its literal prescribed entry.
The fixed reader then returns the original whole $R_P(u)$, with
its unchanged partition, repeated occurrences and blocking guards.

Each execution on $Z_{b_3}$ visits $D$, all $n$ first-scan
positions and all $n$ second-scan positions. Each such visit makes
one paid invocation. Its costs are exactly $2n+1$ and $3+2W_A$.
This fiber is nonempty by Definition 4.1, so these costs are
attained by actual finite origins. Every other execution makes
one or two root queries and costs at most two calls and six
letters. Since $W_A\ge5n$ and $n\ge3$, these are smaller than
the displayed scan costs. There are exactly $n(d+e)+2$ running
states and $2+r$ latches. This proves all of (PCA.67). $\square$

## 30. A strict central-threshold state saving and its execution price

**Proposition 30.1 (a strict subgrid family of full resource points).**
For every integer $t\ge5$, every supplied $A$ of cardinality
$n=4t^2$, and the central threshold $k=2t^2$, compare the following
two preparers for the *same* $\sigma_{A,k}$:

$$
\begin{aligned}
\mathcal R_{\mathrm{grid}}
 &=\bigl(k(n-k+1)+4+r, n+1, 3+W_A\bigr),\\
\mathcal R_{\mathrm{two}}
 &=\bigl(n(4t+1)+4+r, 2n+1, 3+2W_A\bigr).
\end{aligned}
\tag{PCA.74}
$$

Each row is one full attainable point with its own exact uniform
execution maxima. The second row has strictly fewer installed
states than the first. It has larger call and literal maxima, so
the assertion is an installed-state improvement with additional
paid execution, not a coordinatewise improvement of resource points.

Proof. The first row is Theorem 26.1 and the second is Theorem 29.2,
since $\lceil\sqrt{4t^2}\rceil=2t$. The difference of their
installed cardinalities is

$$
\begin{aligned}
k(n-k+1)-n(4t+1)
 &=2t^2(2t^2+1)-4t^2(4t+1)\\
 &=2t^2(2t^2-8t-1)>0.
\end{aligned}
\tag{PCA.75}
$$

For $t\ge5$, $2t^2-8t-1=2t(t-4)-1\ge9$.
Also $2n+1>n+1$ and $3+2W_A>3+W_A$. Arbitrary finite sets of
these cardinalities exist, for instance $A=\{1,\ldots,4t^2\}$,
so this gives a nontrivial infinite central-threshold family on the
original full source domain. At the enlarged execution budgets of
$\mathcal R_{\mathrm{two}}$, both tables are allowed and the
grid's installed count is strictly improvable. No grid-optimality
premise is required. Neither this comparison nor either table pairs
the smaller $H$ with the grid's execution minima. $\square$

## 31. Counted modular chains for the prescribed native consumer

**Assumption 31.1 (a supplied classical chain and its separation).**
For the $n,k$ of Definition 29.1, supply a finite chain MA-program
in Sinha's Definitions 3.14 and 3.17 [printed pp. 31–33][SINHA95].
It has $b\ge1$ boxes with positive integer moduli
$q_1,\ldots,q_b$ and size $S=\sum_{j=1}^b q_j$. Box $j$ has
input and output positions $0,\ldots,q_j-1$. An integer $h$
entering input $s$ leaves at output $(s+h)\bmod q_j$.
Every output is either a sink or is connected by a supplied fixed
map $M$ to an input of box $j+1$; the last box's outputs are sinks.
The source is a supplied input $(j_0,s_0)$; it may be taken in
box one, and unused preceding boxes, if any, still contribute to
$S$ and $b$. In particular the box connections are acyclic.

The chain separates $\{0,\ldots,k-1\}$ and
$\{k,\ldots,n\}$: no sink receives an integer from both sets
when routed from the supplied source. Label a sink zero or one
according to the set reaching it; assign zero to sinks reached by
neither set. This labeling is common table data depending on the
supplied chain and $n,k$, never on the actual native source. A
chain not satisfying this separation is not a premise of the
following upper bound. The integer $h$, the chain inputs and its
abstract routing operation are mathematical specification objects,
not accessible native preparation ports.

**Theorem 31.2 (fully paid native chain interface).** For every supplied
chain of Assumption 31.1 there is, for the same $\sigma_{A,k}$ on
all of $\mathcal U_*$, a finite preparer with

$$
\boxed{\ H=nS+4+r,\qquad p\le nb+1,\qquad
                         \ell\le bW_A+3.\ }
\tag{PCA.76}
$$

Here $H$ is the exact installed count of the specified construction;
the other two expressions are uniform upper bounds, without an
assertion that a native source traverses all boxes. Every box input,
scan position, residue and connection is represented in its counted
states or its fixed four-successor table. It has no additional
mutable configuration.

Proof. Sinha's Proposition 3.10 supplies the modular scan;
Lemma 3.16 and Corollary 3.18 describe its classical Boolean
branching-program connection. The following construction spells out
and prices the native specialization, rather than treating those
Boolean nodes or their interconnections as uncharged native services.

For every box $j$, position $1\le i\le n$ and
$0\le z<q_j$, install a distinct running state $C_{j,i,z}$ with
literal $a_i$ of (PCA.66). Thus there are exactly $nS$ such
states. The states $C_{j,1,s}$ are the representations of all input
positions $s$ of box $j$: they are already in this count, not
additional free input nodes. A state holds the current residue in
its identity, not a separate register retaining the input value.

Let $\Lambda(j,z)$ be the following fixed successor name for an
abstract box output:

$$
\Lambda(j,z)=
\begin{cases}
\widehat e_v,&(j,z)\text{ is a sink with fixed label }v,\\
C_{j+1,1,s},&M(j,z)=(j+1,s).
\end{cases}
\tag{PCA.77}
$$

For each $\varepsilon\in\{0,1\}$ define the installed names

$$
G(j,i,z,\varepsilon)=
\begin{cases}
C_{j,i+1,(z+\varepsilon)\bmod q_j},&i<n,\\
\Lambda\bigl(j,(z+\varepsilon)\bmod q_j\bigr),&i=n.
\end{cases}
\tag{PCA.78}
$$

Install $D,T$, the two original-entry latches and all $r$ further
mandated latches. Start at $D$ with the total four-successor table

| Running state | Absolute literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | $C_{j_0,1,s_0}$ | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |
| $C_{j,i,z}$ | $a_i$ | $G(j,i,z,0)$ | $G(j,i,z,0)$ | $G(j,i,z,1)$ | $G(j,i,z,0)$ |

There is no separate running output node: the box's final paid
query takes exactly the edge specified by (PCA.77). In the sink
case it directly replaces the current running state by its original
entry latch; all sinks with one label may use that same literal
latch. In the connection case it directly replaces it by the
counted first-position state of the next box with the prescribed
input residue. Thus the abstract connection is included in an
ordinary installed successor, with its table bytes separately
priced. There is no silent native transition, extra latch per
abstract sink, input latch, scan reset state, dispatch state,
phase register or uncounted residue. Even modulus one has $n$
installed running states whose $n$ visits are paid. All unreachable
box states and the $r$ unused latches count.

Fix any actual $u\in Z_{b_3}$ and put
$\theta_i=\chi(r_{x_a}(w_i))$, $h=\sum_i\theta_i$, as proof
notation only. For a scan entering box $j$ at $C_{j,1,s}$,
induction gives the residue before position $i$ as
$(s+\sum_{v<i}\theta_v)\bmod q_j$. The last query therefore
takes precisely $\Lambda(j,(s+h)\bmod q_j)$. All subsequent
scans read the same stationary native replies. Induction along the
acyclic chain proves that the run reaches the sink label of the
supplied chain on this same $h$, which is one exactly when $h\ge k$.
This proves the required (PCA.53) for every finite branch image,
including arbitrary sizes, shapes and absent selected nodes.

The $D,T$ rows deal with all other profiles exactly as in Theorem
29.2: $\Pi_3$ and $\Pi_4$ latch one and all other non-scan
profiles latch zero. Thus correctness holds for every original
finite inverse origin, with the same prescribed complete entries
and the fixed whole-row reader. Separation has not been replaced
by a promise on cube inputs: every integer $h$ arising on an
arbitrary native source lies in $\{0,\ldots,n\}$, which is
exactly the supplied chain's entire integer interval.

If the chain on such an $h$ traverses $\nu(h)$ boxes, the native
execution has exactly

$$
q_P(u)=1+n\nu(h),\qquad
\ell_P(u)=3+W_A\nu(h),\qquad 1\le\nu(h)\le b.
\tag{PCA.79}
$$

Every selected literal is submitted once per traversed box, at its
full absolute length; repeated occurrences are charged again.
Acyclicity bounds the number of traversed boxes by $b$. On the
other profiles at most two calls and six letters are used, both
dominated by $nb+1$ and $bW_A+3$ for $n\ge3$, $b\ge1$.
Counting $nS$ scan states, the two running profile states and all
$2+r$ latches proves (PCA.76). If a common running start is named
in advance, label $D$ by that name. No source-dependent
initialization is needed. $\square$

## 32. The classical near-linear state supplier and the unresolved optima

**Corollary 32.1 (uniform near-linear-polylog native state upper).**
There are absolute constants $C,n_0$ such that for every $n\ge n_0$,
every supplied $A$ of cardinality $n$, and every $1\le k\le n$,
a preparer for the same original $\sigma_{A,k}$ on all of
$\mathcal U_*$ has

$$
\begin{aligned}
H&=nS_{n,k}+4+r,\\
S_{n,k}&\le C\frac{\log^3 n}
                      {\log\log n\,\log\log\log n},\\
p&\le nb_{n,k}+1,\qquad
\ell\le b_{n,k}W_A+3,\qquad b_{n,k}\le S_{n,k}.
\end{aligned}
\tag{PCA.80}
$$

The integers $S_{n,k},b_{n,k}$ refer to one and the same supplied
chain for this $n,k$. In particular the native installed count is
$O(n\log^3 n/(\log\log n\,\log\log\log n))+4+r$ uniformly in
threshold. The implicit constant does not depend on $A,k$ or $r$.
For smaller $n$, Theorem 29.2 supplies the explicit finite upper.

Proof. Apply Sinha's [Theorem 3.29, printed p. 41][SINHA95], to the
integer threshold problem on $I=\{0,\ldots,n\}$, of length
$L=n+1$, with the $k$ smallest integers as its low set. Its
high set is exactly $\{k,\ldots,n\}$. That theorem supplies
a chain of size
$O(\log^3 L/(\log\log L\,\log\log\log L))$ separating these
sets, uniformly for the specified threshold and interval. Replacing
$L=n+1$ by $n$ in this asymptotic bound changes only the absolute
constant after increasing $n_0$.

The uniformity used here is also explicit in that supplier's proof:
Proposition 3.28 chooses the moduli using only interval length,
Corollary 3.27 routes the unresolved integers into a shorter
interval, and Theorem 3.29 recurses on that interval with the
size estimate independent of the threshold. These are credited
classical results, not newly asserted generic theorems. Supply
one such chain to Theorem 31.2. Each modulus is a positive integer,
so $b_{n,k}\le\sum_j q_j=S_{n,k}$. This gives every bound in
(PCA.80) on one native table. It yields, if desired, the loose
execution uppers $p\le nS_{n,k}+1$ and
$\ell\le S_{n,k}W_A+3$; no smaller asymptotic scan count or
execution optimum is inferred from the size theorem. $\square$

**Definition 32.2 (two different installed-state minima).** For
$2\le k\le n-1$, retain $H_{\min}(A,k;r)$ of Corollary 27.3,
with no restriction on the finite uniform execution budgets. Let
$H_{\mathrm{exec}}(A,k;r)$ be the least installed cardinality
among preparers that simultaneously satisfy
$p\le n+1$ and $\ell\le3+W_A$. Both minima exist as integers
because Theorem 26.1 supplies such a finite table. They concern
all of Convention 23.2's competitors, including repeated queries,
shared states and cyclic union graphs with sourcewise termination.

**Proposition 32.3 (retained lower bounds and distinct remaining gaps).**
For every $2\le k\le n-1$,

$$
\begin{aligned}
2n+2+r
&\le H_{\min}(A,k;r)\\
&\le\min\{k(n-k+1),\ n(2\lceil\sqrt n\rceil+1)\}+4+r,\\
H_{\min}(A,k;r)
&\le H_{\mathrm{exec}}(A,k;r)
 \le k(n-k+1)+4+r.
\end{aligned}
\tag{PCA.81}
$$

When a separating chain of size $S$ is supplied, the first upper
can additionally include $nS$ in that minimum. For sufficiently
large $n$, Corollary 32.1 gives the corresponding uniform
near-linear-polylog upper on $H_{\min}$. The independent minimum
call and literal upper budgets remain exactly $n+1$ and $3+W_A$.
For $k=2$ and $k=n-1$ both installed minima remain exactly
$2n+2+r$, as in Theorem 27.1. For the remaining general interior
thresholds $3\le k\le n-2$, neither an exact unrestricted
$H_{\min}$ nor an exact $H_{\mathrm{exec}}$ is determined here.

Proof. Reuse Theorem 25.1 for the unrestricted linear state lower
and Theorem 25.2 and Corollary 27.3 for the exact independent
execution minima. Theorems 26.1, 29.2 and, when applicable, 31.2
give separate full attainable resource points; dropping execution
constraints gives their respective uppers on $H_{\min}$. Only
Theorem 26.1 is used for the upper at the simultaneous execution
minima. Restricting competitors cannot lower the infimum of
installed cardinalities, giving
$H_{\min}\le H_{\mathrm{exec}}$. The exact two endpoint values
are direct reuse of Theorem 27.1, including coincident endpoints
when $n=3$. None of the new repeated-scan bounds is paired with
another table's smaller execution costs. No ordered/read-once
lower bound of Wegener or Bryant is imposed on the unrestricted
competitors. Thus the stated inequalities leave precisely the two
general state questions unresolved. $\square$

## 33. Mathematical attribution and the supplied realization contract

**Attribution 33.1 (suppliers and the native quantitative addition).**
The modular routers, modular arithmetic programs, chain programs
and their generic Boolean branching-program translations are
literature-attested: Sinha, *Some Topics in Parallel Computation
and Branching Programs*, Definitions 3.14 and 3.17, Proposition
3.10, Lemma 3.16 and Corollary 3.18, printed pp. 28–33. The
near-linear-polylog size supplier is his Theorem 3.29 and its proof,
printed pp. 39–41, with Proposition 3.28 and Corollary 3.27 as
its explicit prerequisites. His printed p. 42 credits the two-box
exact-division paradigm underlying Lupanov's earlier majority
construction. The present explicit two-scan table is an application
of that classical paradigm, not a new generic threshold or
branching-program result. The [citation-only source note][SINHANOTE]
records this supplier scope. No theorem premise is taken from the
uninspected journal full text associated with DOI
10.1006/jcss.1997.1530.

The source and permission correspondence for these deductions is
NBP Definitions 1.1–1.2 and 9.1, Assumption 9.2, Proposition 9.3,
the every-address occurrence identity (NBP.9.7), Proposition 15.2
and Theorem 15.5; here it is fixed by Definitions 1.1, 4.1–4.2,
Supplier application 4.3, Convention 23.2 and Definition 29.1. These
supply the full original actual domain, unique finite inverse
origins, all eleven profiles, both repeated partners, complete
rows and the unchanged eight-state reader. Lemma 24.1 supplies
actual lower-bound witnesses, and Theorems 25.1–25.2 and 27.1
supply the reused lower and exact endpoint results.

The additional native content is the explicit fully paid point
(PCA.67), its strict central-threshold subgrid consequence
(PCA.74)–(PCA.75), and the counted original-entry modular-chain
interface (PCA.76) with its supplier consequence (PCA.80).
The statements quantify over the entire original fiber and price
all running states, original-entry latches, mandated additional
latches and actual running visits. This is a repository-derived
native quantitative deduction from the credited suppliers; no
literature-wide priority claim is made.

PCA Theorems 12.4 and 14.3 already give finite paid-task
correspondences for a prescribed code under their hypotheses;
NBP §§12–14 already give generic shared-graph correspondences
with their own encoding permissions. Those correspondences are
not reproved here and do not give the displayed quantitative
points. [Finite-reader synthesis, §§11–12][FCS], explicitly
separates selecting a new compatible code from generating an
original prescribed code and supplies no budgeted preparation
optimum. Its freely selected code is not substituted for
$\sigma_{A,k}$ in any statement above.

**Assumption 33.2 (unchanged services and separate prices).** All
operational premises of Assumptions 1.2, 16.1 and 22.2 and Boundary
28.2 remain supplied. The genuine origin/current-register binding,
one authenticated update, acquisition and authentication of the
complete current row and acquired code arguments, lawful pre-cut
native permission, actual export, complete isolation, code-only
handoff, faithful original complete entry and stationary native
service are not obtained from existence of the tables above.
They retain their separate permissions and prices.

The only accessible preparation distinction is the current counted
running or latch state. Every running visit submits its installed
absolute literal and costs one invocation, including a repeated,
constant, root or absent reply. All four successors are installed.
There is no additional source copy, working register, counter,
phase, cursor, decoder, reset, address calculation or unpriced
output-to-input step. Source-independent table design may use
$A,n,k$ and a supplied chain, and never the actual source.

Installed table representation and connections, literal address
bytes, original complete entry contents, whole-row output storage,
initialization, local work, actual handoff and service/isolation
storage retain their separate costs. The fixed reader's eight
states and its fresh calls are a separate phase's resources;
no preparer bound pays for them by omitting their costs. No total
physical-memory, time or energy bound, arbitrary-code extractor,
exact general state optimum or completion of the broader native
relational-fiber problem follows from (PCA.67)–(PCA.81).

[SINHA95]: https://dada.cs.washington.edu/research/tr/1995/08/UW-CSE-95-08-02.pdf
[SINHANOTE]: ../../../Library/ConceptDynamics/sinha1995branching.md
[FCS]: FIB_NATIVE_FINITE_READER_CODE_SYNTHESIS.md

## 追加锚（本行以下为增补区）
## 34. Two-sided saturation of every live cube prefix

**Definition 34.1 (live histories at both execution minima).** Fix
$n\ge5$, $3\le k\le n-2$, the supplied $A$ of Definition 23.1,
and $r\ge0$. Throughout §§34–35, $P$ is any preparer of Convention
23.2, correct for the original $\sigma_{A,k}$ on the whole
$\mathcal U_*$, with

$$
q_P(u)\le n+1,\qquad \ell_P(u)\le3+W_A
\quad(u\in\mathcal U_*).
\tag{PCA.82}
$$

There is no restriction on its installed addresses, repeated literals,
unused states, shared successors or union cycles. Its actual runs on
Lemma 24.1's cube are used only as lower witnesses. In a finite
execution history, let $S$ be the set of coordinates exposed by any
query in $E_i$, let $h$ be their number of ones, and let
$m=|S|-h$. An exposure includes a selected child query: all three
addresses at either occurrence determine that same bit by (PCA.55).
A history ending just before the next invocation is *live* if its
cube completions have both prescribed bits, equivalently

$$
h<k,\qquad m\le n-k.
\tag{PCA.83}
$$

Histories include all paid invocations already made, including
cube-constant ones. Their sets and counts are proof notation, not
accessible running coordinates. A live history cannot end at a
latch: all its cube completions follow that history, whereas their
two different original entries are required.

**Lemma 34.2 (opposite-code comparisons on both sides).** For every
cube vector $\theta$ of weight $k-1$, there is an actual origin
$u^-_\theta\in\Pi_3$ of prescribed bit one such that every word
distinguishing it from $u_\theta$ belongs to

$$
\mathcal C_c\cup\{RLR\},\qquad
\mathcal C_c=RLL\mathcal W\ \cup\ RRL\mathcal W.
\tag{PCA.84}
$$

For every cube vector $\eta$ of weight $k$, there is an actual
origin $u^+_\eta\in Z_*$ of prescribed bit zero such that every
word distinguishing it from $u_\eta$ belongs to
$\mathcal C_3=RLR\mathcal W$. Both distinguishing sets contain
$RLR$, and their intersection is exactly $\{RLR\}$. Every correct
run on either of these cube vectors therefore has a distinguishing
invocation outside $\bigcup_iE_i$, of length at least three.

Proof. Keep $x_a=B_\theta$ and $x_{b_j}=D_j$ for $j=1,2,4$
in (PCA.56), and replace $x_c$ by beta and $x_{b_3}$ by alpha,
as in Theorem 25.2. All six values remain different. NBP Proposition
9.3 gives a genuine finite inverse in $\Pi_3$, with its complete
predecessor row $R_3$. Only the two $c$ cones and the $b_3$
cone can change. In the latter cone the old beta and new alpha
are leaves, so every nonempty suffix gives absent on both. Thus
only its root $RLR$ can distinguish them there. The required bits
are zero on $u_\theta$ and one on this comparison origin.

For the positive side choose a branch image $D_3$ different from
every $B_\eta$ in the finite cube and from $D_c,D_1,D_2,D_4$.
The infinite branch-image supply of NBP Proposition 15.2 allows
this choice. In (PCA.56), with vector $\eta$, replace only the
beta $x_{b_3}$ by $D_3$. All six values are now distinct branch
images. NBP Proposition 9.3 supplies an actual inverse in $Z_*$,
whose prescribed bit is zero by (PCA.12), whereas $u_\eta$ has
bit one. Only the $b_3$ cone changes.

The every-address occurrence identity (NBP.9.7) proves these
statements for all finite suffixes, including traversal past leaves.
Words shorter than three remain exterior branches. The $c$ and
$b_3$ cones are disjoint from every $E_i$ and from one another.
At $RLR$ the respective reply pairs are beta/alpha and beta/branch,
so that word belongs to both distinguishing sets and is their only
common member. All repeated occurrences use the same whole value;
all different-class disequalities and the full current row persist.

Finally, if a cube run had no distinguishing invocation, the comparison
source would follow its identical finite path to the identical literal
entry latch. This contradicts the opposite prescribed bit and the
injectivity of the original entry map. The required extra invocation
is therefore on that same cube run, not on a separately maximized
execution. $\square$

**Theorem 34.3 (live-prefix saturation and the unique live profile
literal).** Every live history of Definition 34.1 extends to each of
two actual cube runs, one of final weight $k-1$ and one of final
weight $k$, with the following properties.

1. Every proper prefix before the last distinct selected-coordinate
   query is live. Each completed run uses exactly $n$ selected
   invocations, one at each coordinate, and exactly one further
   invocation. Their total costs are exactly $n+1$ and $3+W_A$.
2. Every invocation from a live history queries either a previously
   unexposed coordinate $i$, at exactly $LLLw_i$ or $LRLw_i$,
   or the literal $RLR$. There is at most one nonselected invocation
   during the live portion. In particular a selected child, a repeated
   bit, an unrelated constant or root word, and a second profile
   invocation are excluded there.
3. On the two saturated completions in part 1, the unique nonselected
   invocation is $RLR$ and precedes the $n$th selected invocation.

Proof. Start with the given live history. For a negative completion,
answer each first exposure of a new coordinate by one until the
total number of exposed ones is $k-1$, and then by zero.
For a positive completion, instead answer new coordinates by zero
until the total number of exposed zeros is $n-k$, and then by one.
Previously exposed coordinates keep their values. Lemma 24.1 gives
the actual reply for each such bit, including at selected children;
every other word receives its fixed cube reply.

For the negative rule every proper exposed prefix has at most $k-1$
ones and at most $n-k$ zeros; its last fresh answer is the
$(n-k+1)$st zero. For the positive rule the analogous last answer
is the $k$th one. Thus both predicates remain possible until the
$n$th distinct exposure. These rules are consistent with the
starting history by (PCA.83). Every finite response history has
actual cube completions.

A latch before all $n$ exposures would give one entry to both
required bits. Nor can a running state first repeat: all bit values
used between its two visits have then been fixed, and any actual
completion would repeat that stationary deterministic loop forever.
The finite installed state set and sourcewise termination therefore
force all $n$ distinct exposures. Their resulting vectors have the
claimed weights, and their remaining paths are actual terminating
cube runs.

Lemma 34.2 supplies, on each of these very runs, one further
distinguishing invocation outside the selected supports. The $n$
distinct selected invocations charge at least $W_A$ letters, and
that further invocation charges at least three. Both bounds in
(PCA.82) are consequently equalities. There can be no repeated
coordinate or second nonselected invocation anywhere on either
saturated run. Every selected word must have its minimum length
$s_i+4$, attained in $E_i$ only at its two occurrence roots;
the unique nonselected word has length exactly three.

Apply these two completions at a live history just before any
specified next invocation. That invocation's installed word is the
same in both completions, even if its next bit answer differs.
If selected, it is fresh and is one of the two shortest roots.
If nonselected, it is the sole nonselected word on both completed
runs, and so must distinguish both respective comparisons of
Lemma 34.2. Their intersection forces that word to be $RLR$.
A prefix containing two nonselected invocations would itself
occur in a saturated completion, which has only one. This proves
parts 1 and 2 without identifying any installed states or
declaring their union acyclic.

It remains to exclude postponing the profile invocation until after
all $n$ selected calls on a saturated run. If it were so postponed,
the prefix through those calls would consist solely of the $n$
shortest selected roots, with cost $n$ calls and $W_A$ letters.
Hold their whole value $x_a=B_\theta$ fixed and choose three
actual origins with $x_c=\beta$, the same branch values at
$b_1,b_2$, and, respectively,

$$
(x_{b_3},x_{b_4})=(D_3,D_4),\quad
(\alpha,D_4),\quad(D_3,\alpha).
\tag{PCA.85}
$$

Choose the branch values to avoid $B_\theta$ and one another.
These are actual $Z_c,\Pi_3,\Pi_4$ origins by NBP Proposition
9.3. Their required bits are respectively $0,1,1$. They all follow
that selected-only prefix, since both $a$ occurrences are identical.
Each has at most one invocation and three letters left. A shorter
word gives the common exterior branch. A length-three word at
$a,b_1,b_2$ or either $c$ occurrence is common to all three.
The $b_3$ root distinguishes only $\Pi_3$, and the $b_4$ root
only $\Pi_4$. No one allowed invocation can separate $Z_c$ from
both positive origins. Immediate latching also cannot do so.
This contradicts whole-domain correctness and (PCA.82).

Thus the sole nonselected invocation precedes the last selected
one; its starting history is live. Part 2 identifies it as $RLR$.
This proves part 3. The sources in (PCA.85), like those in Lemma
34.2, are actual full-fiber comparison origins, not extra runtime
ports or restrictions on upper inputs. $\square$

## 35. A consumed saturation invariant in shared-state exclusion

**Theorem 35.1 (a two-history exclusion for installed running states).**
Let two live cube histories of the same preparer end at the same
installed running state. Write their exposed coordinate sets as
$S,T$ and their numbers of exposed ones as $h,g$. Set

$$
a=|S\setminus T|,\quad b=|T\setminus S|,\quad
U=[n]\setminus(S\cup T),\quad u=|U|.
$$

Then the following integer intersection must be empty:

$$
[0,u]\ \cap\
[k-h-b,k-h-1]\ \cap\
[k-g-a,k-g-1]\ \cap\ \mathbb Z.
\tag{PCA.86}
$$

Also, if $S=T$, then necessarily $h=g$. These are necessary
conditions for sharing, not a sufficient sharing criterion or a
converse construction.

Proof. Suppose first that an integer $t$ lies in (PCA.86).
Fix one assignment on $U$ with exactly $t$ ones. In the first
history, after all of $U$ has these values, the unexposed part
$T\setminus S$ still has the nonconstant residual threshold

$$
1\le k-h-t\le b.
$$

For the second history the corresponding assertion is
$1\le k-g-t\le a$ on $S\setminus T$. Hence after any partial
exposure of that fixed $U$ assignment both histories still have
zero and one completions: complete the rest of $U$ as fixed and
vary their respective remaining private sets. This argument does
not require their old assignments on $S\cap T$ to agree.

Follow the successors from the common state using that assignment
on $U$. Every cube-constant word has the same reply in both
histories. A selected word in $S\cup T$ would repeat a coordinate
already exposed in at least one of the two still-live histories.
Theorem 34.3 excludes that invocation. The same theorem excludes
any selected child, any other nonselected word except $RLR$,
a second $RLR$, or a repeat within $U$. Consequently the common
continuation can use at most the $u$ fresh coordinates of $U$
and one $RLR$. Both histories remain live throughout these
possibilities, so a latch is impossible. After those finitely many
possibilities are exhausted, no permitted next invocation remains.
This contradicts correctness and sourcewise termination. This is
the use of live-prefix saturation in the state-merger argument;
mere equality of residual names is not a premise.

Now suppose $S=T$ but, say, $h>g$. Apply Theorem 34.3 to the
first history, taking its positive saturated completion of total
weight $k$. Give the second history the same values on every
coordinate outside $S$. Both actual cube sources then follow the
same suffix from the alleged common state. Indeed, until its last
fresh selected query the first run is live, so it queries only
previously unread coordinates and possibly $RLR$; these replies
agree on the two sources. On that saturated run all coordinates
are read exactly once, and its unique $RLR$ precedes the last
one. It therefore latches immediately after that last selected
invocation, with no further source distinction. The second source
reaches the same latch, but its total weight is
$k-h+g<k$. Their required entries differ, a contradiction.
Interchanging the histories covers $g>h$. $\square$

**Corollary 35.2 (two explicit classes of forbidden live mergers).**
Two live histories with the same exposed set and different hit
counts cannot share a running state. Two live histories with the
same number of exposed coordinates and the same hit count, but
different exposed sets, cannot share a running state either.

Proof. The first statement is the second part of Theorem 35.1.
For the second put $d=|S|=|T|$ and $h=g$. Then
$a=b>0$ and $n-d=a+u$. Liveness gives

$$
1\le k-h\le n-d=a+u.
$$

The integer interval $[k-h-a,k-h-1]$ is nonempty, its upper
endpoint is nonnegative and its lower endpoint is at most $u$.
It therefore intersects $[0,u]$. This makes (PCA.86) nonempty,
contrary to Theorem 35.1. $\square$

**Proposition 35.3 (the precise limitation of the exclusion).** The
conclusions of Theorem 35.1 do not entail that an installed state
determines an exposed set, hit count or live residual function.
There is a whole-domain preparer at both execution minima with
two live histories at one state for which both the exposed sets
and hit counts differ.

Proof. Proposition 36.1 below constructs such a preparer. At its
common state take

$$
S=\{1,2,5\},\ h=0,\qquad
T=\{1,3,4\},\ g=3,\qquad n=7,\ k=4.
\tag{PCA.87}
$$

Here $a=b=u=2$. The two threshold intervals in (PCA.86) are
$[2,3]$ and $[-1,0]$, so the exclusion does not apply. The
two live residuals in (PCA.87) are the different functions proved
in Proposition 36.1. Thus the empty-intersection case is a real
remaining sharing class, not a license to assert a converse.
$\square$

## 36. A balanced-literal live merger on the entire original domain

**Proposition 36.1 (same-state different live residuals with both
execution maxima attained).** For the existing prescribed code
$\sigma_{A,4}$ with $A=\{1,2,3,4,5,6,7\}$, there is a full
Convention 23.2 preparer with

$$
H=47+r,\qquad p=8,\qquad \ell=59=3+W_A.
\tag{PCA.88}
$$

Two live actual cube histories reach one common running state,
with the exposed data of (PCA.87). Their respective residuals
on unexposed coordinates are

$$
\theta_3\theta_4\theta_6\theta_7
\quad\hbox{and}\quad
\theta_2\vee\theta_5\vee\theta_6\vee\theta_7.
\tag{PCA.89}
$$

Some subsequent actual executions repeat previously exposed
selected coordinates. All literals, successors, running states
and latches are installed and counted. The construction is
larger than the old grid, whose count here is $20+r$.

Proof. Write $a_i=LLL L^iR$ and $c_i=|a_i|=i+4$.
For every source in $Z_{b_3}$ put
$\theta_i=\mathbf1_{\{r_{x_a}(L^iR)=\mathsf{branch}\}}$.
These seven bits are proof notation on an arbitrary branch image,
not a promise that it has a comb shape. Put

$$
X=\{2,5\},\quad Y=\{3,4\},\quad R=\{6,7\},\qquad
c_X=c_2+c_5=15=c_3+c_4=c_Y,
\quad c_1=5,\quad c_R=21,\quad W_A=56.
\tag{PCA.90}
$$

Use the two original-entry latches, denoted $L_0=\widehat e_0$,
$L_1=\widehat e_1$. Every selected-query state below installs
the word $a_i$ in its indicated coordinate $i$. Its zero
successor is installed separately for each of alpha, beta and
absent; its one successor is installed for branch. Thus the two
successor columns specify all four actual native edges.

Four disjoint fallback blocks use only the selected-query part
of Theorem 26.1's threshold grid, with the following supplied
coordinate orders and thresholds. They share only $L_0,L_1$.

| Block and its start | Ordered remaining coordinates | Required remaining hits | Installed running states |
| --- | --- | --- | --- |
| $G_1$ | $(3,4,5,6,7)$ | $3$ | $3(5-3+1)=9$ |
| $G_2$ | $(3,4,6,7)$ | $3$ | $3(4-3+1)=6$ |
| $G_3$ | $(2,4,5,6,7)$ | $3$ | $3(5-3+1)=9$ |
| $G_4$ | $(2,5,6,7)$ | $2$ | $2(4-2+1)=6$ |

In each block the pair $(h,m)$ names a separately installed grid
state, reading the $(h+m+1)$st coordinate of that displayed list.
Its branch successor advances $h$ or latches $L_1$ at its required
hit count; its other three successors advance $m$ or latch $L_0$
when too few hits remain possible. These are precisely the
successors (PCA.62), with the block's list and threshold substituted.
No counter or computed address is installed alongside these states.

Install the following thirteen further selected-query states,
all distinct from every fallback state.

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $P_1$ | $1$ | $P_2$ | $P_3$ |
| $P_2$ | $2$ | $P_5$ | $G_1$ |
| $P_5$ | $5$ | $V$ | $G_2$ |
| $P_3$ | $3$ | $G_3$ | $P_4$ |
| $P_4$ | $4$ | $G_4$ | $V$ |
| $V$ | $6$ | $V_0$ | $V_1$ |
| $V_0$ | $7$ | $O_2$ | $J$ |
| $V_1$ | $7$ | $J$ | $B_3$ |
| $O_2$ | $2$ | $O_5$ | $L_1$ |
| $O_5$ | $5$ | $L_0$ | $L_1$ |
| $J$ | $1$ | $L_0$ | $L_1$ |
| $B_3$ | $3$ | $L_0$ | $B_4$ |
| $B_4$ | $4$ | $L_0$ | $L_1$ |

The first five states form the head. The last eight form its shared
continuation. Each table entry is a fixed state name; subscripts
denote no auxiliary running memory.

For completeness install the original two profile states, start at
$D$, and use their unchanged four-successor table, replacing only
the threshold-grid start by $P_1$.

| State | Absolute literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $L_1$ | $P_1$ | $T$ | $L_0$ |
| $T$ | $RRR$ | $L_1$ | $L_0$ | $L_0$ | $L_0$ |

Every mandated additional latch is installed, unused, and counted.
The Boolean symbols in the proof specify successor choices; handoff
carries the original complete entry $e_0$ or $e_1$, not a new
one-bit encoding.

We first prove correctness for every Boolean vector of selected
replies. The four fallback entries are reached with, respectively,

$$
(\theta_1,\theta_2)=(0,1),\quad
(\theta_1,\theta_2,\theta_5)=(0,0,1),\quad
(\theta_1,\theta_3)=(1,0),\quad
(\theta_1,\theta_3,\theta_4)=(1,1,0).
$$

Their already acquired hit counts are respectively $1,1,1,2$.
The displayed fallback thresholds are therefore exactly the
remaining requirements for four hits, and their lists contain
every unqueried coordinate once.

There are exactly two other routes to $V$:

$$
\lambda:\ \theta_1=0,\ \theta_2=\theta_5=0,
\qquad
\mu:\ \theta_1=1,\ \theta_3=\theta_4=1.
\tag{PCA.91}
$$

On $\lambda$, four hits require every bit in $Y\cup R$ to be
one. On $\mu$, the remaining task is OR on $X\cup R$.
Both are nonconstant on their cube completions, proving liveness
and (PCA.89). The selected query at $V$ has not yet been made.

For the correctness proof only, let $t=\theta_6+\theta_7$.
The three scan states $V,V_0,V_1$ route $t=0$ to OR on $X$,
$t=1$ to the single query $J$ of $\theta_1$, and $t=2$ to
AND on $Y$. This is the fixed table above, not a runtime sum.
On $\lambda$ the first two exits return zero because
$\theta_X=00$ and $\theta_1=0$; the last exit computes exactly
the necessary AND on $Y$. On $\mu$ the first exit computes
the necessary OR on $X$; the other two return one because
$\theta_1=1$ and $\theta_Y=11$. Thus every route computes
the original four-hit predicate.

This verification holds for every possible Boolean vector, hence
for the seven branch indicators of every finite branch image in
$Z_{b_3}$, regardless of interior shape, depth, leaf labels or
absent selected nodes. The occurrence identity (NBP.9.7) identifies
each $a_i$ reply with that actual indicator. Outside $Z_{b_3}$,
$D$ directly handles $\Pi_3$. When $b_3$ is branch the only
code-one remaining profile is $\Pi_4$, detected at $T$ by alpha
at $b_4$. All other profiles on that route latch zero, exactly as
in Theorem 26.1. These are all eleven original profiles.
The root absent edges are installed even though those roots are
reached on this domain. Each selected alpha, beta and absent reply
uses its own installed zero edge. No finite address is removed
from the native permission or replaced by a computed relative one.

For the execution bounds, any fallback route reads an initial
segment of distinct coordinates and then each remaining coordinate
at most once, so it uses at most seven selected calls and $W_A$
letters. On a shared route the head costs three selected calls.
The $R$ scan costs two. The final OR or AND uses at most two
more, and $J$ uses one. There are therefore at most seven selected
calls. A $\lambda$ head has literal charge $c_1+c_X$ and a
$\mu$ head has $c_1+c_Y$. Their scan adds $c_R$.
Either two-query exit adds at most $c_X=c_Y$; the single-query
exit adds $c_1\le c_X=c_Y$. Consequently every shared route
also has selected literal charge at most $W_A$. This is where
the balanced absolute-literal equality in (PCA.90) is needed:
a repeat is paid by omitting a group of equal total length,
not by treating that repeat as free.

Adding $D$ gives at most eight calls and $3+W_A=59$ letters
on a selected path. A nonselected profile route has at most two
calls and six letters. Every route terminates; in fact this
constructed installed graph is acyclic. Lemma 24.1's actual
all-zero cube origin follows

$$
D,\ P_1,\ P_2,\ P_5,\ V,\ V_0,\ O_2,\ O_5,\ L_0.
\tag{PCA.92}
$$

It has seven selected calls, including real repeats of coordinates
$2,5$, and selected charge
$c_1+2c_X+c_R=56$. This one genuine source attains both
maxima in (PCA.88).

There are $5$ head states, $8$ shared-continuation states and
$9+6+9+6=30$ fallback states, hence $43$ selected-query
states. Adding $D,T$, the two original-entry latches and all
$r$ mandated latches gives exactly $47+r$. No uncounted selector,
phase state, working register or stored source has been used.
The original reader remains its separate eight-state apparatus,
with all five complete canonical predecessor-row outputs, two
fresh calls at most and six fresh letters at most. All original
holes, equalities, different-class disequalities and blocking guards
in those outputs remain as in Convention 23.2. The table generates
the original prescribed entry on each identical source; it does
not select another compatible encoder.

Finally, Lemma 24.1 supplies actual cube origins for every
completion of either history (PCA.91). The common state $V$
therefore genuinely merges two live, different residuals on the
original domain. On $\lambda$ with $\theta_6=0$, the predicate
is already zero, whereas on $\mu$ with that same reply it still
depends on $X$ and $\theta_7$. Both enter the same $V_0$.
Replacing that state globally by the former history's zero latch
would corrupt the latter history. The repeats in (PCA.92) belong
to a suffix that is essential on other histories. This is a
live merger before certification, rather than insertion of a
disposable paid tail after a common certificate. Its larger count
does not disprove a no-larger normalization theorem or the grid
optimum; either assertion would require its own proof. $\square$

## 37. Supplier hypotheses and the remaining state comparison

**Proposition 37.1 (scope of the resulting state comparison).** Under
Definition 32.2, for $3\le k\le n-2$ every candidate table at
both execution minima obeys Theorem 34.3 and the exclusions of
Theorem 35.1. Nevertheless these results do not give an
original-state quotient in which every live state has one
threshold residual, and do not determine
$H_{\mathrm{exec}}(A,k;r)$ or $H_{\min}(A,k;r)$.

Proof. The first claim applies the preceding theorems to exactly
the competitors of Definition 32.2. The second claim about an
original-state quotient follows from Proposition 36.1: its same
state $V$ has the two different nonconstant restrictions (PCA.89).
An assignment of one residual to that original state cannot
represent both, and first-certificate truncation at $V_0$
conflicts on the two histories just proved. Splitting states,
changing their query words, or replacing an entire table may
produce another representation, but preservation of installed
cardinality, the prescribed code and both execution caps would
then be additional obligations.

In particular no bound stronger than (PCA.81) is deduced here.
The grid remains an upper at both execution minima. The example
(PCA.88) has a larger installed count and supplies a structural
counterexample, not an improved resource optimum. The unrestricted
minimum also still allows the already supplied paid multiple-scan
constructions of §§29–33. $\square$

**Attribution 37.2 (classical hypotheses and source-specific
deductions).** Wegener, *The Complexity of Boolean Functions*,
Chapter 14 §4, Definition 4.1 and Theorems 4.1 and 4.3,
[printed pp. 423–425][WBP], owns the optimal synchronous
read-once representation of symmetric functions and its residual
count. The proof on printed p. 424 expressly uses that every
graph path in a BP1 is realized by an input, a property it
does not claim for general branching programs. Bryant,
[§2, Definition 1][BRY], requires strictly increasing argument
indices on nonterminal edges. These are genuine additional
hypotheses. Live-prefix freshness proved here is not a proof
that an arbitrary installed native graph meets them; Proposition
36.1 already obstructs the direct residual assignment, even
with an acyclic constructed graph.

Sinha, *Some Topics in Parallel Computation and Branching
Programs*, [§2.1.3, printed p. 17][SINHA95], allows cycles
provided no semantic path contains a cycle, and records the
Pippenger leveling construction with $(l+1)s$ states for size
$s$ and semantic length $l$. That construction's copies do
not establish a cardinality-preserving comparison for the
native installed-state question. The classical results remain
their suppliers' results; no read-once optimality theorem is
reproved or imported beyond its hypotheses.

The native mathematical suppliers are NBP Proposition 9.3,
(NBP.9.7), Proposition 15.2 and the unchanged reader of Theorem
15.5; here their contracts are Definitions 1.1–2.2 and 4.1–4.2,
Convention 23.2 and Lemma 24.1. Theorem 26.1 supplies the
reused fallback grids and profile front. The added deductions
are the two-sided actual comparisons and their all-prefix
saturation, its consumption in (PCA.86), and the balanced-literal
full-domain live merger (PCA.88). Their consumer is the
installed-state gap of Definition 32.2 and Proposition 32.3. They are
repository-derived ordinary-paper arguments, without a current
kernel or worldwide-priority claim.

[Bounded native preparer synthesis, Theorems 8.3 and 9.1 and
Convention 11.3][BPS34], and [Polynomial origin certificates,
§9, Lemma 9.1][POC34], preserve an attained joint relation
and SAME budgets while allowing different pointwise generated
bits on different matched actual sources. Their SOME-code
normalization supplies no preservation of the independently
prescribed $\sigma_{A,k}$ on the identical source.
[Native weight optimization, §8, Open problem 8.4][NWO34],
retains its distinct local-to-global compatibility and
native-completion obligations. No entropy, certificate or
finite-relaxation optimum from those contracts is substituted
for a native shared-state exclusion here.

All services and separate prices in Assumption 33.2 remain
supplied: actual origin/version binding and update, acquisition
and authentication, export, isolation, code-only handoff,
faithful complete reader entry and stationary truthful service.
Every installed running, latch and whole-output state retains
its appropriate phase's charge; every actual invocation and
absolute literal is paid. Table representation, literal storage,
entry and whole-output contents, initialization, handoff,
service storage, time and energy keep their separate prices.
Neither the lower comparisons nor the full-domain construction
adds an archive, source copy, address operation, decoder,
counter or unpriced phase coordinate.

[BPS34]: FIB_BOUNDED_NATIVE_PREPARER_SYNTHESIS.md
[POC34]: FIB_NATIVE_POLYNOMIAL_ORIGIN_CERTIFICATES.md
[NWO34]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_WEIGHT_OPTIMIZATION.md

## 追加锚（本行以下为增补区）
## 38. Exact five-position third-hit installed cardinality

**Scope 38.1 (the unchanged native contract).** Fix five distinct positive
positions

$$
A = {s₁ < s₂ < s₃ < s₄ < s₅},   cᵢ = sᵢ + 4,   W_A = ∑ᵢ cᵢ,   k = 3,   r ≥ 0.
$$

A competitor is any Convention 23.2 preparer for the original prescribed
code on the whole unbounded one-image fibre. It is a finite stationary graph
of fixed absolute words with all four native replies installed, a common
running start, sourcewise termination, the original complete entries and
reader, and no restriction on order, read-once behaviour, acyclicity, source
shape, repeated words, shared successors or unused states. Every installed
running or latch state and every invocation is charged, including constants,
absence, roots and repeats. Assume only the simultaneous execution caps

$$
p_P ≤ 6,   ℓ_P ≤ 3 + W_A.   (PCA.93)
$$

The reader, handoff, all complete rows, equality and disequality classes,
strict-prefix guards, services and separately priced resources are exactly
those of §§1–4 and 23. The finite cube below is a lower-bound family only.

For a cube prefix before an effective selected invocation, let S be the set
of selected coordinates already exposed, let h be the number of their one
replies, and put d = |S|. Call the prefix live when both threshold values
remain possible. For n = 5 and k = 3 this is

$$
h ≤ 2,   d − h ≤ 2.   (PCA.94)
$$

A state carrying the literal RLR can be followed on the cube through its
constant beta edge; whenever a state is called selected below, this common
edge has already been followed. Thus a possible profile call is still
charged and cannot create a free state identification.

**Lemma 38.2 (all-weight comparison and profile timing).** Every actual cube
run, for every θ ∈ {0,1}⁵, has an invocation outside ⋃ᵢ Eᵢ and hence has a
call of length at least three. Under (PCA.93), a live prefix extends to actual
weight-two and weight-three cube runs whose selected portions contain exactly
five distinct selected invocations and exactly one nonselected invocation,
namely RLR, before the fifth selected invocation. In particular the first
selected coordinate is common to all cube runs.

**Proof.** Let uθ be the actual origin supplied by Lemma 24.1. If |θ| ≤ 2,
keep xₐ = Bθ and replace x_c by beta and x_b₃ by alpha. The six class values
remain distinct, NBP Proposition 9.3 supplies an actual Π₃ origin, and every
selected address in every Eᵢ has the same reply as on uθ. The prescribed
entries differ. If |θ| ≥ 3, keep all selected replies and replace the beta at
b₃ by a fresh branch image, chosen distinct from the finitely many values in
this comparison. NBP Proposition 9.3 supplies an actual zero-profile origin
in Z₍*₎, again with the same selected replies and the opposite prescribed
entry. Thus a correct path on uθ must visit a word outside all Eᵢ; the address
classification (PCA.55) gives length at least three. This argument is for
every cube weight, not only the two boundary weights.

Starting at any live prefix, answer fresh selected coordinates by ones until
two ones have been exposed for the negative completion, and by zeros until
two zeros have been exposed for the positive completion; thereafter answer
fresh coordinates with the opposite value. The two response rules are actual
cube completions by Lemma 24.1 and preserve (PCA.94) until all five
coordinates have been exposed. A latch before that point would give one
entry to both required values. A first repeated running state would repeat a
stationary deterministic loop on an actual completion, contradicting
sourcewise termination. Hence each completion reads all five selected
coordinates once. Theorem 34.3 excludes a second nonselected invocation on
these live continuations. The all-weight comparison supplies one additional
paid invocation, so the call cap forces exactly five selected invocations and
one nonselected invocation on each saturated completion; the literal cap
forces selected charge W_A and nonselected length three.

It remains to locate that nonselected invocation. If it were postponed until
after all five selected roots, the selected prefix would already cost five
calls and W_A letters, leaving at most one call and three letters. Keep the
same selected replies and choose the three actual comparison origins used in
(PCA.85): a zero-profile origin with x_c = beta, a Π₃ origin differing at
b₃, and a Π₄ origin differing at b₄. A word shorter than three is common to
all three. A length-three word in the b₃ cone separates only the Π₃ origin,
and one in the b₄ cone separates only Π₄; every other available word is
common on this comparison. No single final invocation can therefore produce
the three required entries. The unique nonselected invocation must precede
the fifth selected query, and its cube reply is beta. The first selected word
is consequently fixed after the common start, possibly after this one common
profile call. ∎

**Lemma 38.3 (nested live supports cannot merge).** Two live cube histories
of the same preparer ending at one running state cannot have S ⊂ T.

**Proof.** Write h and g for the hit counts in S and T, put b = |T ∖ S| > 0,
and let U = [5] ∖ T. Complete the T history to weight two by assigning
exactly 2 − g ones on U. Its saturated suffix queries only U and the already
common profile call, and then enters the zero entry. Give the S history the
same values on U and assign one to every coordinate in T ∖ S. It follows
that identical suffix from the common state, because none of those private
coordinates is queried in the suffix. Correctness of the zero entry gives
h + b + (2 − g) < 3, hence h + b ≤ g.

Conversely complete the T history to weight three by assigning 3 − g ones on
U, and give every coordinate in T ∖ S value zero for the S source. The same
suffix now enters the one entry. Correctness gives h + (3 − g) ≥ 3, hence
h ≥ g. These inequalities contradict b > 0. The two completions are actual
finite origins, and their old assignments on S ∩ T need not be compared:
the common suffix reads only U and the profile word. ∎

**Lemma 38.4 (scoped reciprocal saturated-prefix balance).** Suppose two
incomparable live histories end at one running state, with exposed sets
S,T satisfying S ∖ T = {a}, T ∖ S = {b}, and nonempty common unread set
U = [5] ∖ (S ∪ T). Suppose their respective residuals and private old
values are

$$
AND({b} ∪ U),\quad a = 0,
\qquad OR({a} ∪ U),\quad b = 1.
$$

Then their complete actual continuations under (PCA.93) force cₐ = c_b.
The assertion concerns only this AND/OR geometry and these private
polarities; it makes no cost-balance claim for other mergers.

**Proof.** The OR history has exactly two old ones.
Complete all its unread coordinates {a} ∪ U by zero. This is precisely its
negative saturated extension from Theorem 34.3: it remains live until the
last of these coordinates, reaches total weight two, and reads every
selected coordinate once at an occurrence root. Its only other invocation
is RLR, before its last selected query. After that query it goes directly
to the original zero-entry latch, since its six paid calls are exhausted.
The selected suffix from the common state therefore queries exactly
{a} ∪ U, in whatever order its stationary table dictates, with all replies
beta. It never queries T again and has no post-certification query.

Now complete the AND history by giving U the same zeros and giving its
unread b either value. Lemma 24.1 realizes this as an actual origin. From
the common state it follows exactly the OR source's suffix: its old a is
zero, its U replies are the same, and every nonselected cube reply is
constant. Induction through the fixed successors gives the same complete
suffix and terminal latch. Assignments on S ∩ T need not agree because
this suffix never queries them. On this AND source the selected prefix
queries S once, and the replayed suffix queries {a} ∪ U once. Thus it
makes five selected invocations, repeats a, omits b, and has selected
literal charge W_A + cₐ − c_b. This repeat can occur after that source is
already certified zero; it is permitted and charged, not excluded by
live-prefix freshness. Lemma 38.2 supplies on this very source at least
one nonselected call of length at least three. Consequently

$$
3 + W_A + cₐ − c_b ≤ ℓ_P ≤ 3 + W_A,
\qquad cₐ ≤ c_b.
\tag{PCA.95}
$$

For the reverse inequality the AND history has exactly two old zeros:
its threshold residual requires every unread coordinate. Complete its
unread {b} ∪ U by one. Theorem 34.3's positive saturated extension stays
live until the last such coordinate, has total weight three, queries all
five selected coordinates once at their roots, and ends directly at the
original one-entry latch with its single paid RLR already made. Replay
that suffix on the OR history with U all one and its unread a arbitrary.
The old b = 1 agrees with the fresh b = 1, and the suffix reads neither
S ∩ T nor a. The same fixed-successor induction is therefore valid.
This OR source repeats b, omits a, makes five selected invocations and
pays selected charge W_A + c_b − cₐ. Its own mandatory nonselected call
adds at least three letters. The literal cap gives c_b ≤ cₐ.

Both charges concern complete runs on their respective actual sources;
no costs from different executions are added. RLR need not have occurred
at the same prefix position in the two histories. If replay would produce
two nonselected calls, five selected calls already make that impossible
under p_P ≤ 6; if it would produce none, Lemma 38.2 is contradicted.
In every permitted replay its nonselected charge is at least three.
By Lemma 2.3 a terminating replay cannot revisit a running state, so its
repeated coordinate is queried at a distinct installed state; both states
and both invocations count. The two inequalities prove the claimed equality. ∎

**Theorem 38.5 (nine reachable selected cells and the exact bound).** Every
preparer in Scope 38.1 has at least nine distinct installed running states
whose literals lie in ⋃ᵢ Eᵢ. Consequently

$$
H ≥ 13 + r.   (PCA.96)
$$

Together with Theorem 26.1, this gives

$$
H_exec(A,3;r) = 13 + r   (|A| = 5).   (PCA.97)
$$

**Proof.** By Lemma 38.2 the first selected coordinate is a fixed x. The
following nine live cells are reachable by actual cube prefixes:

$$
\{(d,h)\}=\{(0,0),(1,0),(1,1),(2,0),(2,1),(2,2),
             (3,1),(3,2),(4,2)\}.
\tag{PCA.98}
$$

The displayed strings record their selected replies, not runtime registers:

| d | h | one reachable reply prefix |
|---:|:---:|:---|
| 0 | 0 | ε |
| 1 | 0, 1 | 0, 1 |
| 2 | 0, 1, 2 | 00, 01, 11 |
| 3 | 1, 2 | 001, 011 |
| 4 | 2 | 0011 |

Every prefix in the table satisfies (PCA.94), so Lemma 24.1 realizes it and
sourcewise termination prevents an earlier latch or repeated state.

Histories with the same exposed set and different hit counts cannot merge by
Theorem 35.1; histories with the same d,h and different exposed sets cannot
merge by Corollary 35.2. We also use the following direct budget observation.
Once a branch has made five selected invocations, Lemma 38.2 supplies a
mandatory nonselected invocation, so no sixth selected invocation is available
under p_P ≤ 6. If two actual sources then have the same reply at a state but
opposite required entries, a nonselected cube word has the same reply on both
sources, and a sixth selected query is forbidden.

First, Lemma 38.3 excludes proper containment. Since every exposed set after
the first query contains x, this disposes of all comparisons involving the
d = 0 or d = 1 cells. A d = 4 set either contains an earlier set, or has no
coordinate outside its union with that earlier set; Theorem 34.3 then forbids
a common next selected query. Thus the only possible cross-depth comparison
left is an incomparable d = 2 set and an incomparable d = 3 set.

Consider the three d = 2 histories. Let a₀ be the second coordinate after
reply 0 at x, and a₁ the second coordinate after reply 1. Write 00, 01, 10, 11
for the two selected replies. If a₀ = a₁, the three displayed d = 2 cells
have the same support and their different hit counts exclude sharing by
Theorem 35.1. Hence in the following cross-branch comparisons assume
a₀ ≠ a₁. The pairs 00,01 and 10,11 have the same
support and are excluded by Theorem 35.1; 01,10 have the same d,h and
different support and are excluded by Corollary 35.2. If 00 and 10 shared a
state, their private old values would both be zero. The only common unread
coordinates are two coordinates z,w. After either first common query, choose
reply one; both histories remain live, so the next effective selected query is
the other common coordinate. With both replies one, the 00 history still
needs its private coordinate, while the 10 history is already positive. The
common next query must therefore be the private coordinate of the 10 history.
Give it value zero also on the 00 completion. This is the fifth selected
invocation on both paths; their beta replies agree and the budget observation
forbids any later selected split, so the opposite required entries are
impossible.

If 01 and 11 shared a state, their private old values would both be one. Give
the first common unread query, and then the second, reply zero. The 01 history
is then forced to zero, while the 11 history must query the private coordinate
of the 01 history. Give that fresh coordinate value one, which is also the old
value in the 01 history. This is the fifth selected invocation on both paths;
the common branch reply and the budget observation again contradict the
opposite required entries.

It remains to compare 00 and 11. Put a = a₀, b = a₁ and let z,w be
the two common unread coordinates. The histories have supports {x,a} and
{x,b}, old private values a = 0 and b = 1, and residuals
AND({b,z,w}) and OR({a,z,w}). Lemma 38.4 applies with U = {z,w}.
Explicitly, the 11 history completed by a = z = w = 0 has weight two
and must read all three of those coordinates before its zero latch.
Replaying its entire suffix on 00 repeats a and omits b, forcing
cₐ ≤ c_b. The 00 history completed by b = z = w = 1 has weight three
and must read all three before its one latch. Replaying on 11 repeats b
and omits a, forcing c_b ≤ cₐ. These are both required actual executions
of one alleged shared graph. Distinct selected positions have distinct
costs cᵢ = sᵢ + 4, so their simultaneous inequalities are impossible.

This exclusion allows post-certification discrimination. For example, if
the common suffix first reads z = 1,w = 0, both histories have become
constant with opposite values after four selected invocations. A fifth
selected invocation at a distinct installed running state querying the old
coordinate x returns beta on 00 and branch on 11 and can directly choose
the two original latches. That state and its invocation both count.
With an earlier RLR its call count is six. Its respective selected charges
are W_A + c_x − c_b and W_A + c_x − cₐ, so both local paths can obey
the literal cap, for instance when c_x is least. No common-reply argument
excludes this repeat. Instead, the two complete saturated continuations
above exclude the merger regardless of the choices on this mixed branch
or any other decided branch. Repeated roots, selected children or further
cube-constant queries on such branches remain ordinary paid operations;
they cannot change either forced extremal charge. Thus the three displayed
d = 2 cells require three different installed states.

For d = 3, a one-hit history has an AND residual on its two unread
coordinates and a two-hit history has an OR residual. Equal supports are
already excluded. Since both supports contain x, different supports have
intersection size one or two. In the size-one case each history has two
private coordinates and there is no common unread coordinate. In Theorem
35.1 put a = b = 2, u = 0, h = 1, g = 2. The intersection (PCA.86) is
[0,0] ∩ [0,1] ∩ [−1,0], which contains the integer zero. That geometry
is therefore excluded by the existing theorem.

In the size-two case the private coordinates are a (exposed in the AND
history) and b (exposed in the OR history), with one common unread
coordinate z. At z = 0 the AND history is forced zero and the
OR history must query a. If the old AND value of a were one, choose fresh
a = 1 in the OR source; both replies would be branch at the fifth selected
visit, and the budget observation forbids a later split between the opposite
entries. Hence the old AND value is a = 0. At z = 1 the OR history is
forced one and the AND history must query b. If the old OR value of b were
zero, choose fresh b = 0 in the AND source; both replies would be beta at the
fifth selected visit, and the budget observation again forbids a later split.
Hence the old OR value is b = 1. Lemma 38.4 now applies with U = {z}:
complete the OR source by a = z = 0 and the AND source by b = z = 1.
Their saturated suffixes replay on the opposite histories with exactly the
two paid repeats established in that lemma. They force cₐ = c_b, impossible.
Therefore the two d = 3 cells are distinct.

It remains to compare d = 2 and d = 3. For supports of sizes two and three,
with one common unread coordinate, Theorem 35.1's intersection is

$$
[0,1] ∩ [1 − h, 2 − h] ∩ [2 − g, 2 − g],
$$

where h is the d = 2 hit count and g the d = 3 hit count. For h ∈ {0,1,2}
and g ∈ {1,2} it is nonempty, and hence sharing is forbidden, except for
(h,g) = (0,2) and (h,g) = (2,1).

For (h,g) = (0,2), incomparable supports have the form S = {x,a} and
T = {x,b,c}. The first history has x = a = 0; the second must have x = 1
and exactly one of b,c equal to one, since equal replies at x would force the
same second coordinate. Let z be the unique common unread coordinate. Give z
reply one. The d = 2 history still needs both b,c, while the d = 3 history is
already positive. If the common next query is b and its old value in the d = 3
history is zero, give fresh b = 0 to the d = 2 source. The beta reply is
common, the first source is forced zero and the second requires one, and the
second source has now made five selected visits; the budget observation rules
out any later selected split. If that old value is one, give fresh b = 1: the
common branch reply leaves the first history live and the second history after
five selected visits. The first requires the other private query c, which
would be a sixth selected visit on the second source and is forbidden by its
mandatory nonselected invocation. The same argument applies if the common
query is c.

For (h,g) = (2,1), the first history has x = a = 1; the second has x = 0
and exactly one of b,c equal to one. Give the common unread coordinate z reply
zero. The d = 2 history needs one of b,c, while the d = 3 history can never
reach three if its queried private coordinate is zero and is forced zero. If
the common query is b and its old value in the d = 3 history is zero, give
fresh b = 0 to the d = 2 source. The common beta reply leaves the first source
live and the second source forced zero. Any correct common continuation must
query the first source's remaining private coordinate c, but the second source
has already made five selected visits and has a mandatory nonselected visit,
so this would be a forbidden sixth selected query; latching would fail the
first source. If that old value is one, give fresh b = 1: the common branch
reply gives the first source one while the second is forced zero, and the same
five-visit budget rules out a later split. Querying c is symmetric. Thus no
d = 2 state can be a d = 3 state.

All nine cells in (PCA.98) therefore require distinct installed selected
running states. Each is a state with a word in one of the disjoint supports
Eᵢ, so there are at least nine such states. Lemma 7.1 requires, separately,
one running state in the b₃ occurrence cone and one in the b₄ occurrence
cone; those cones are disjoint from all Eᵢ and from one another. The two
original complete-entry latches and the r mandated additional latches are
also installed and counted. Hence H ≥ 9 + 2 + 2 + r = 13 + r.

Theorem 26.1 with n = 5 and k = 3 supplies the full-domain grid with nine
selected states, the two profile states, the two original latches and the r
mandated latches, and it attains p = 6 and ℓ = 3 + W_A. Its proof covers
every original profile, every finite address, all four replies, the complete
reader entries and all output guards. Thus the lower and upper bounds
coincide. No ordering, read-once or acyclicity property of an arbitrary
competitor was used. ∎

## 39. Attribution, boundary and falsifiers for the bounded result

The actual-cube and occurrence facts are supplied by PCA Lemma 24.1 and NBP
Proposition 9.3, occurrence identity (NBP.9.7) and Proposition 15.2;
the saturation and profile-timing facts are PCA Theorem 34.3, the interval exclusion is PCA Theorem 35.1, the mandatory
profile states are PCA Lemma 7.1, and the attaining grid is PCA Theorem 26.1.
The new source-specific content is the nested-support exclusion, the expanded
five-position same-depth and cross-depth case analysis, the reciprocal
saturated-suffix charges for the stated single-private-coordinate AND/OR
geometry, and their direct nine-state installed-state count.

Wegener, *The Complexity of Boolean Functions*, Chapter 14 §1,
Definitions 1.1–1.2, and §4, Theorems 4.1 and 4.3, gives the classical residual
count for BP1/read-once branching programs. Bryant, *Graph-Based Algorithms
for Boolean Function Manipulation*, §2 Definition 1, imposes strictly
increasing variable indices. Sinha, *Some Topics in Parallel Computation and
Branching Programs*, §2.1.3, distinguishes semantic paths from union-graph
cycles and gives a leveling blow-up. Those suppliers do not apply their
hypotheses to the unrestricted native competitors here. The proof of (PCA.97)
uses no classical BP1 transfer, no fixed variable order and no acyclicity
assumption; its count is made on the original installed states.

The reciprocal balance statement is not a global cost-balance theorem. It
retains the AND/OR residuals, the two private old polarities, the common
unread suffix and the two execution caps. The six-position unequal-cost
candidate and any other incomparable merger geometry are not accepted here.
No assertion is made for n ≥ 6, for a no-larger whole-table replacement, or
for the unrestricted H_min. Acquisition, authentication, export, isolation,
entry, stationary service, physical memory, time and energy remain separately
supplied and priced. The result is an ordinary-paper bounded parameter
theorem, not a kernel, physical or whole-goal claim.

A direct falsifier is a correct original-contract preparer for some five-point
A satisfying p_P ≤ 6, ℓ_P ≤ 3 + W_A and H ≤ 12 + r. At proof level, a
reachable shared state in any excluded cell pair, a nested-support merger
whose two saturated completions violate one of the displayed inequalities, or
a legal completion escaping one of the forced-polarity cases would refute the
corresponding step. The preceding statements do not settle the unresolved
larger-parameter or uncapped problems.

## 追加锚（本行以下为增补区）
