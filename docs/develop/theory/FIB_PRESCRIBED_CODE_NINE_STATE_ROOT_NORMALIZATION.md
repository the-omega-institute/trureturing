# Prescribed binary codes: nine-state root normalization

> This is an append-only `generic-v1` reference volume. Its locators are
> determined from its own Markdown bytes. Existing text is retained;
> corrections and extensions belong in new numbered sections after the final
> append anchor.

## 1. Scope and mathematical status

This volume proves three statements on the original repeated-partner
one-image fiber. Every prescribed binary code served by an arbitrary-literal
stationary Moore reader with at most nine installed states and at most two calls is
served, with the identical pointwise code, by a representative-root reader
with nine installed states and at most four calls. Independently of that
premise, a terminating representative-root reader within nine states exists
exactly when the code is constant on at least one whole positive fiber.
When all four positive fibers attain both bits, the unrestricted terminating
root minimum is exactly ten states, with four calls sufficient.

The proofs are ordinary paper mathematics. This reference input carries no
Lean kernel certification or executable mathematical verification. Mathematical
authorship is by the sole Codex CLI author; the canonical suppliers identified
below retain ownership of their reused results. The additional deductions are
`repo-derived`, without a claim of worldwide originality.

The owning native volume is [Native cut-birth provenance and literal past-row
recovery][NBP], abbreviated NBP. The bounded-call comparison is [Prescribed
binary codes: a nine-state escape from root-only two-call reading][NRE],
abbreviated NRE. The acquisition comparison is [Native prescribed-code
acquisition on the original one-image fiber][PCA], abbreviated PCA. Numbered
citations below specify exactly which results are reused. Neither a root
profile nor an output label replaces the original source domain or the
complete predecessor row.

## 2. The original native fiber and all complete outputs

**Definition 2.1 (finite sources, literal replies and image inverse).**
Reuse NBP Definitions 1.1–1.2 and Proposition 9.3. The sources are all finite
nonempty ordered terms

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{NRN.1}
$$

In the native Boolean convention, true and false name alpha and beta;
false and true address letters name $L$ and $R$. A literal address is any
finite word in $L,R$, including $\varepsilon$. Its actual reply is the leaf
label, $\mathsf{branch}$ at a pair, or $\mathsf{absent}$ outside the finite
tree. Every word is legal, and any nonempty continuation at either leaf is
absent. At every existing occurrence $p$,

$$
r_t(pw)=r_{t|_p}(w).
\tag{NRN.2}
$$

The supplied disjoint image grammar and inverse are

$$
\mathcal I=\rho[\mathcal T]::=\beta\mid E\mid
                  \langle\mathcal I,\mathcal I\rangle,
\qquad
\delta(\beta)=\alpha,\quad\delta(E)=\beta,\quad
\delta\langle y,z\rangle=\langle\delta y,\delta z\rangle
\quad(y,z\in\mathcal I).
\tag{NRN.3}
$$

These finite recursive maps are inverse on their stated domains. In
particular, $\rho$ is injective, alpha is not an image, and beta is the only
leaf image. Write $\mathcal B=\mathcal I\setminus\{\beta\}$ for the finite
branch images. NBP Theorem 3.3 and Proposition 15.2 supply infinitely many
different members: $T_m=\rho^m\alpha$ for $m\ge2$. Thus any finite list of
forbidden values can be avoided when choosing branch images. The inverse
constructs mathematical origins; it is not an available physical action.

**Definition 2.2 (complete rows and the entire comparison domain).**
For a finite prefix-free cut $P$, the row $R_P(t)$ retains the complete
exterior after replacing each reached cut subtree by its occurrence hole,
and the complete partition of equal hidden subtrees. Different classes
assert disequality. An unreached cut member has an exposed concrete leaf
at a strict prefix as its absence guard. Equal subtrees at different
addresses remain different occurrences. In lexicographic order of the
reached holes, a class is named by its first hole's zero-based position;
these positions are recomputed after restriction and need not be consecutive.

Fix exactly the depth-three cut and current row of NBP Definition 9.1:

$$
\begin{aligned}
P&=\{L,R\}^3,\qquad R_*=(C_*,\pi_*),\\
\pi_*&=\{\{LLL,LRL\},\{LLR\},\{LRR\},
                \{RLL,RRL\},\{RLR\},\{RRR\}\}.
\end{aligned}
\tag{NRN.4}
$$

Here $C_*$ is the complete binary exterior with eight occurrence holes at
depth three. The six class aliases, representatives and full occurrence
sets are as follows.

| Class | Representative $p_d$ | All occurrences |
| --- | --- | --- |
| $a$ | $LLL$ | $LLL,LRL$ |
| $c$ | $RLL$ | $RLL,RRL$ |
| $b_1$ | $LLR$ | $LLR$ |
| $b_2$ | $LRR$ | $LRR$ |
| $b_3$ | $RLR$ | $RLR$ |
| $b_4$ | $RRR$ | $RRR$ |

For six pairwise different actual finite values $x_d$, set

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{NRN.5}
$$

The domain and whole target are

$$
\mathcal U_*=
 \{u\in\mathcal T:R_P(\rho u)=R_*\},
\qquad t_u=\rho u,\qquad F(u)=R_P(u).
\tag{NRN.6}
$$

Every finite origin satisfying this equation belongs to the domain. There
is no size, depth, rank, branch-family, predecessor or additional history
promise. The legal-row fiber and inverse identify this domain with all
injective valuations $x$ for which $\mathscr S(x)\in\mathcal I$, by
$u=\delta(\mathscr S(x))$. This identification preserves both repeated
partner occurrences and all six-class disequalities.

**Definition 2.3 (the five whole rows stored at Halts).**
Reuse NBP Proposition 9.3, exposed completely in NRE Definition 2.2. Put
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$. The exteriors of $R_h=(C_h,\pi_h)$
are exactly

$$
\begin{aligned}
C_0={}&\left\langle
 \left\langle\langle\square_{LLL},\square_{LLR}\rangle,
                  \langle\square_{LRL},\square_{LRR}\rangle\right\rangle,
 \left\langle\langle\square_{RLL},\square_{RLR}\rangle,
                  \langle\square_{RRL},\square_{RRR}\rangle\right\rangle
\right\rangle,\\
C_1={}&\left\langle
 \left\langle\beta,\langle\square_{LRL},\square_{LRR}\rangle\right\rangle,
 \left\langle\langle\square_{RLL},\square_{RLR}\rangle,
                  \langle\square_{RRL},\square_{RRR}\rangle\right\rangle
\right\rangle,\\
C_2={}&\left\langle
 \left\langle\langle\square_{LLL},\square_{LLR}\rangle,\beta\right\rangle,
 \left\langle\langle\square_{RLL},\square_{RLR}\rangle,
                  \langle\square_{RRL},\square_{RRR}\rangle\right\rangle
\right\rangle,\\
C_3={}&\left\langle
 \left\langle\langle\square_{LLL},\square_{LLR}\rangle,
                  \langle\square_{LRL},\square_{LRR}\rangle\right\rangle,
 \left\langle\beta,\langle\square_{RRL},\square_{RRR}\rangle\right\rangle
\right\rangle,\\
C_4={}&\left\langle
 \left\langle\langle\square_{LLL},\square_{LLR}\rangle,
                  \langle\square_{LRL},\square_{LRR}\rangle\right\rangle,
 \left\langle\langle\square_{RLL},\square_{RLR}\rangle,\beta\right\rangle
\right\rangle.
\end{aligned}
\tag{NRN.7}
$$

The entire partitions are

$$
\begin{aligned}
\pi_0&=\{\{LLL,LRL\},\{LLR\},\{LRR\},
                        \{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_1&=\{\{LRL\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_2&=\{\{LLL\},\{LLR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_3&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RRL\},\{RRR\}\},\\
\pi_4&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL\},\{RLR\}\}.
\end{aligned}
\tag{NRN.8}
$$

Every pair of different blocks remains disequal. The canonical naming and
absence data, with the hole orders made explicit, are

| Whole row | Ordered reached holes | Canonical name vector | Absent cuts and concrete guard |
| --- | --- | --- | --- |
| $R_0=R_*$ | $LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,0,3,4,5,4,7)$ | None |
| $R_1$ | $LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LLL,LLR$; beta at $LL$ |
| $R_2$ | $LLL,LLR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LRL,LRR$; beta at $LR$ |
| $R_3$ | $LLL,LLR,LRL,LRR,RRL,RRR$ | $(0,1,0,3,4,5)$ | $RLL,RLR$; beta at $RL$ |
| $R_4$ | $LLL,LLR,LRL,LRR,RLL,RLR$ | $(0,1,0,3,4,5)$ | $RRL,RRR$; beta at $RR$ |

Thus $R_j$, $j>0$, replaces precisely the pair of holes at $q_j$ by a
concrete beta; its partition is $\pi_*|_{P\setminus\{q_jL,q_jR\}}$ with
recomputed names. The other occurrence of its repeated partner remains an
old hole. The rows have different reached sets, so all five are distinct.
Each Halt below stores one of these entire rows, with its exterior,
partition, naming and guards. No source-dependent decoder completes it.

**Supplier 2.4 (exhaustive actual profiles and whole-target identity).**
Apply NBP Propositions 9.3 and 15.2 on exactly (NRN.6). Write
$g(j)=a$ for $j\in\{1,2\}$ and $g(j)=c$ for $j\in\{3,4\}$. The eleven
nonempty disjoint sets partitioning the entire domain are

$$
\begin{aligned}
\Pi_j:\quad&x_{b_j}=\alpha,\quad x_{g(j)}=\beta,
       \quad\text{the other four values are in }\mathcal B
       &&(1\le j\le4),\\
Z_d:\quad&x_d=\beta,
       \quad\text{the other five values are in }\mathcal B
       &&(d\in\{a,c,b_1,b_2,b_3,b_4\}),\\
Z_*:\quad&\text{all six values are in }\mathcal B.
\end{aligned}
\tag{NRN.9}
$$

Within each set, every choice of the indicated finite branch images is
allowed subject to the original pairwise disequalities. Every such tuple
has the actual finite origin $\delta(\mathscr S(x))$. Its whole target is
$R_j$ on $\Pi_j$ and $R_0$ on every zero set $Z_d,Z_*$. The native image
grammar forces the four depth-two blocks to be images; a nonimage child
can only be the alpha in an $E$ block, with its forced beta partner.
The complete partition permits at most one such right class. These are
the supplied full-fiber facts, including their sufficiency and inverse,
rather than new classification results.

Every address shorter than three reads the common exterior branch. Every
other address is uniquely $pw$ with $p\in P$ and has the actual reply
$r_{x_{[p]}}(w)$ by (NRN.2). We call $[p]$ its queried class and $w$ its
suffix. This accounts for all exterior, repeated-occurrence, arbitrarily
deep and absent queries. Empty-suffix queries are class-root queries.

## 3. Prescribed acquisition, faithful entry and paid stationary reading

**Assumption 3.1 (original two-phase services).**
Keep NBP Assumptions 9.2 and 10.6, Definition 15.1, and NRE Assumption 3.1.
Exactly one authenticated genuine $\rho$ update binds the same actual
origin $u\in\mathcal U_*$ to the same current register $t_u$. The root,
cut and version are fixed; there is no reset, rotation, source replacement,
arbitrary edit or subsequent update. Authentication certifies this binding
without revealing the origin inside the fiber. The current row is lawfully
acquired on this stationary version.

Before the access cut, a producer genuinely possesses either the lossless
finite current tree, or $R_*$ and one acquired finite subtree value for each
of its six classes, all from that same version. Partition equalities are
comparisons of these acquired finite terms. Fix one specified lawful finite
computation on these data, and prescribe its complete exported value

$$
\sigma:\mathcal U_*\longrightarrow\{0,1\}.
\tag{NRN.10}
$$

This code may depend on internal finite structure and may attain only one
bit. The producer computes and actually exports exactly this code with
the current row before losing access to the acquired values. The reader
receives the original pointwise value; no replacement coloring is allowed.

A supplied lawful common entry exposes exactly the prescribed complete
code and common $P,R_*$ and controls. These inputs are recoverable at entry.
No other source-dependent identity, predecessor, alpha marker, acquired
term, trace, cache, old output, archive, pointer, allocation, control field,
acquisition order or count, length, meter, timing or update packet is
accessible. Fields determined by the declared payload add no distinction;
any further accessible source field changes this contract. Inaccessible
material need not be physically erased.

During reading the same register is stationary, and its only source port
is the four-reply literal port of Definition 2.1. There is no equality,
image, provenance, generation, inverse or additional subtree port. Every
invocation is paid, including repeats, absences, leaf continuations and
words already used in acquisition. Every actual origin in the full domain
must terminate with its entire $F(u)$.

Lawful acquisition, acquired-term computation, authentication, version
binding, installation, actual export, complete isolation, faithful entry
and authentic continuing native service are separately supplied and priced.
An absorbing producer stop supplies no resume operation: any reader entry
after it is a separate supplied invocation. A mathematical representation
of the code or row constructs none of these services.

**Definition 3.2 (the entire counted runtime).**
A stationary Moore reader consists of a finite disjoint installed set
$\mathcal K=Q\sqcup H$ and common fixed tables

$$
\begin{aligned}
\operatorname{addr}&:Q\longrightarrow\{L,R\}^{*},\\
\operatorname{next}&:Q\times
 \{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}
                  \longrightarrow\mathcal K,\\
\operatorname{out}&:H\longrightarrow\{\text{complete rows at }P\},\\
\iota&:\sigma[\mathcal U_*]\longrightarrow\mathcal K.
\end{aligned}
\tag{NRN.11}
$$

The entry on $u$ is exactly $\iota(\sigma(u))$. Entry recoverability means
that $\iota$ is injective on the attained code range. At a Read state one
actual invocation at its fixed literal is made and its reply chooses the
fixed successor. At a Halt the fixed entire row is returned without a call.
All four successor constants are installed at every Read, including
unattained replies. Every installed Read and Halt counts, including unused
states and different Halts with identical outputs. Every running visit
costs one invocation.

After entry, the current member of $\mathcal K$ is the entire mutable
accessible source-dependent memory. There is no surviving code copy,
reply register, address register, computed address, independent program
counter, phase, clock, counter, history, archive, table selector or output
decoder. There is no free state transition. Shared states, early Halts,
repeated literals and cycles in unions of different-source paths are
permitted, subject to actual termination on each source.

An arbitrary-literal reader may install any finite native word. A
representative-root reader may install only the six representatives in
Definition 2.2. Both use the same state and entry contract and exactly the
same $\sigma(u)$. State cardinality and calls do not price table bytes,
address construction, storage or transmission, whole-output representation,
transition work, producer workspace, service time or physical resources.

## 4. The exact unrestricted nine-state root criterion

**Lemma 4.1 (stationary paths and the installed budget).**
Every terminating run visits each Read state at most once. Every correct
reader on $\mathcal U_*$ needs at least five Halts. Consequently a correct
terminating reader within nine installed states has at most four Reads
and at most four calls on every source, even without a predeclared call
bound.

Proof. On a fixed stationary source each installed literal has one fixed
reply, so a repeated Read state repeats its deterministic suffix forever.
Termination excludes this repetition; this is NBP Proposition 12.5's
per-source argument. The five distinct attained complete rows in
Definition 2.3 require five different fixed-output Halts. All other
installed states still count. Subtraction gives the Read bound, and the
no-repetition fact gives the call bound. This reasoning does not assert
that the union of paths on different sources is acyclic. $\square$

**Theorem 4.2 (whole-positive-fiber criterion).**
For any prescribed binary code under Assumption 3.1, including a code with
one attained value, a correct terminating representative-root reader with
at most nine installed states exists if and only if

$$
\exists j\in\{1,2,3,4\}\ \exists z\in\{0,1\}\quad
             \forall u\in\Pi_j,\ \sigma(u)=z.
\tag{NRN.12}
$$

When this condition holds, nine installed states and at most four calls
suffice. Necessity continues to hold if the other partner occurrence roots
and exterior-only queries are also permitted.

Proof of sufficiency. Choose $j,z$ as in (NRN.12), and a fixed ordering
$(i_1,i_2,i_3,i_4)$ of the four indices with $i_1=j$. Install four Reads
$Q_{i_1},Q_{i_2},Q_{i_3},Q_{i_4}$ and five Halts $H_0,\ldots,H_4$.
Their entire Read table is

| Read | Fixed actual literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $Q_{i_t}$, $1\le t<4$ | $p_{b_{i_t}}$ | $H_{i_t}$ | $Q_{i_{t+1}}$ | $Q_{i_{t+1}}$ | $Q_{i_{t+1}}$ |
| $Q_{i_4}$ | $p_{b_{i_4}}$ | $H_{i_4}$ | $H_0$ | $H_0$ | $H_0$ |

For each $0\le h\le4$, set $\operatorname{out}(H_h)=R_h$, meaning all
of (NRN.7)–(NRN.8) and the naming and guard table, stored directly at that
Halt. The actual literals are $p_{b_1}=LLR$, $p_{b_2}=LRR$,
$p_{b_3}=RLR$, $p_{b_4}=RRR$. Initialize $z$ at $Q_{i_1}$ and, if the
other value is attained, initialize $1-z$ at $Q_{i_2}$. These entries
are distinct, so the complete bit is recoverable there without a later
bit copy. For a one-value code only the first entry is required.

On every actual source, a tested right root is alpha precisely at its
positive index, if one exists. Entry $z$ tests all four indices. The other
entry omits only $j$, and its code cannot occur on $\Pi_j$. Each entry
therefore returns the correct $R_h$ on every original source, including
all six beta placements in the zero sets, the all-branch zero set and
every admissible internal branch filling. All representatives are reached,
but every absent successor is installed nevertheless. The two entries
use at most four and three actual calls, respectively. All nine installed
states count whether or not every state is reached for this particular
code. No free control step or output decoding is used.

Proof of necessity. Suppose instead that every $\Pi_j$ attains both
bits and a terminating root reader within nine states succeeds. Its two
entries $e_0,e_1$ are distinct Reads: either bit occurs with all four
different positive targets, so neither entry can be a Halt. Lemma 4.1
allows at most four installed Reads.

Each right class $b_j$ must have a Read. Otherwise the root profiles of
$\Pi_j$ and $Z_{g(j)}$ agree at every installed query: they differ only
at $b_j$. On the $\Pi_j$ profile both entry executions must return
$R_j$, since each bit is actually attained there. Root-only behavior
depends only on that profile, not on the hidden finite fillings. Both
entries consequently return $R_j$ on the zero profile as well, contradicting
its actual target $R_0$. This comparison includes any partner queries;
the two partner occurrences have identical replies. Exterior-only words
are shorter than three here and have the same branch reply everywhere.

Thus the four Reads are exactly one at each right root. There is no room
for a partner, exterior, repeated or additional Read. Choose any actual
source in $Z_*$ and let $z$ be its code. Its finite run from $e_z$ ends
at an $R_0$ Halt. It must visit every right Read. If it omitted $b_j$,
an actual source in $\Pi_j$ with code $z$ would give branch at every
queried right root on that path, and would reach the same wrong Halt.
Stationarity makes this a path through all four different Reads once.

The other entry is a different Read in this same four-Read path, strictly
later than its first state. Let $b_i$ be the first state's queried class.
A $\Pi_i$ source carrying the other bit exists. Starting at that later
entry, it follows the all-branch suffix of the path, which omits $b_i$,
and returns $R_0$. Its target is $R_i$, a contradiction. No call cap or
global acyclicity assumption was made. This proves (NRN.12). $\square$

**Theorem 4.3 (exact ten-state unrestricted minimum in the mixed case).**
If $\sigma[\Pi_j]=\{0,1\}$ for each $j$, the least installed state
count of any correct terminating representative-root reader is exactly
ten. A ten-state reader uses at most four calls on every origin.

Proof. Theorem 4.2 excludes every budget at most nine without imposing a
call limit. For the upper, install five Reads $D_0,D_1,Q_2,Q_3,Q_4$ and
the same five complete-output Halts $H_0,\ldots,H_4$. Use the two different
entries $\iota(0)=D_0$, $\iota(1)=D_1$. The entire Read table is

| Read | Fixed actual literal | alpha successor | beta successor | branch successor | absent successor |
| --- | --- | --- | --- | --- | --- |
| $D_0$ | $LLR$ | $H_1$ | $Q_2$ | $Q_2$ | $Q_2$ |
| $D_1$ | $LLR$ | $H_1$ | $Q_2$ | $Q_2$ | $Q_2$ |
| $Q_2$ | $LRR$ | $H_2$ | $Q_3$ | $Q_3$ | $Q_3$ |
| $Q_3$ | $RLR$ | $H_3$ | $Q_4$ | $Q_4$ | $Q_4$ |
| $Q_4$ | $RRR$ | $H_4$ | $H_0$ | $H_0$ | $H_0$ |

The distinct first Reads faithfully hold the two bits at entry and have
identical successors; their duplication is charged. Each entry tests
all four possible positive indices, returns their complete row on alpha,
and returns the complete $R_0$ if all are non-alpha. Supplier 2.4 proves
correctness on the whole fiber, for every zero placement and branch
filling. Every call is paid, and the code has no separate surviving copy.
All ten states count. This gives the matching upper and hence the exact
minimum. It makes no assertion of ten-state sufficiency at three calls.
$\square$

## 5. Two-entry orientation and actual-source variation

**Definition 5.1 (installed reply vector and orientation).**
Fix one arbitrary-literal table and its entry map. Its reply vector at
an actual source lists the truthful replies at all installed Reads,
including unused ones. Equal vectors give identical behavior from each
fixed entry, even when an entry is not the prescribed one on that source.
If a vector is realized by a source of target $R_0$ and a source of
target $R_j$, correctness requires opposite bits on those sources. Both
entry executions on that vector therefore terminate within the prescribed
bound and return exactly $\{R_0,R_j\}$. Call the bit whose entry returns
$R_j$ the positive orientation. Every positive source realizing the
vector must carry that bit. This definition asserts validity of both
entries only when the two actual sources establish it.

**Lemma 5.2 (disjoint stationary paths and one-Read variation).**
On a reply vector where two entries terminate with different whole
outputs, their running-state paths are disjoint. If two vectors each
have entry-output pair $\{R_0,R_j\}$ and differ at at most one installed
Read, their positive orientations agree.

Proof. If the two paths on one fixed vector met at a Read, its stationary
deterministic suffix would be the same for both entries, giving the same
terminal output. Thus they cannot meet. If only Read $K$ changes between
two vectors, at least one of the disjoint entry paths on the first
avoids $K$. Every reply along that whole path is unchanged on the second
vector. The same entry therefore has the same output there. Since both
vectors have the same two different outputs, the entries cannot exchange
which output they return. A change at no Read is included. $\square$

**Lemma 5.3 (fresh buffers connect the whole legal branch domain).**
Fix some coordinates of an injective tuple in one profile (NRN.9).
All legal choices for its remaining branch coordinates are connected by
changes of one coordinate at a time. Consequently, if throughout a
positive profile the entry-output pair is $\{R_0,R_j\}$, and variation
of each free branch coordinate changes replies at at most one Read,
the prescribed code is constant on that entire profile. The same
conclusion applies with further branch coordinates fixed.

Proof. For two endpoint tuples choose one distinct buffer in $\mathcal B$
for each free coordinate, avoiding every value in either endpoint and
every fixed coordinate. Infinitude of $\mathcal B$ supplies these buffers.
Move each coordinate to its buffer, then move each buffer to its desired
endpoint value. At each move the tuple is injective and satisfies exactly
the same profile. Supplier 2.4 gives an actual finite origin at every
intermediate tuple; both occurrences of a repeated class receive the same
value. Lemma 5.2 preserves the orientation at each move, and correctness
identifies that orientation with the original positive code. Unqueried
coordinates affect no Read. A branch-root query has constant branch
reply and contributes no varying reply. $\square$

**Lemma 5.4 (two actual zero companions).**
Each of the following conditions gives, for every actual source in
$\Pi_j$, an actual zero-target source with the identical installed
reply vector.

1. No Read queries class $b_j$.
2. No Read queries its partner $g(j)$, and every Read querying $b_j$
   has nonempty suffix.

In either case both entries on every $\Pi_j$ vector have output pair
$\{R_0,R_j\}$, within two calls when the original correctness bound is
two calls.

Proof. For item 1 replace $x_{b_j}=\alpha$ by a fresh branch image,
leaving its beta partner and all other values fixed. This is an actual
$Z_{g(j)}$ filling and changes no queried value. For item 2 replace
$x_{b_j}=\alpha$ by beta and replace its beta partner by a fresh branch
image. This is an actual $Z_{b_j}$ filling. All queried continuations
at either alpha or beta are absent, and the changed partner is unqueried.
Choose the new branch value outside the finite list of other values.
Every tuple stays injective, every repeated partner occurrence receives
its class's value, and the inverse of Supplier 2.4 supplies the actual
finite origin with its complete zero row. Definition 5.1 gives the
two-entry conclusion. No preservation of $\sigma$ under replacement is
assumed: correctness forces the companions to carry opposite bits.
$\square$

**Lemma 5.5 (mandatory queried classes).**
A correct binary-code table must query at least one right class in
each of $\{b_1,b_2\}$ and $\{b_3,b_4\}$. If exactly two different
right classes are queried, a partner must also be queried.

Proof. If neither right class in one pair is queried, hold its partner
at beta and every queried class value fixed. There are actual fillings
with no alpha, alpha at the first omitted right class, and alpha at the
second omitted right class. Choose all required branch values distinctly
and fill every unused slot with fresh values. Supplier 2.4 places these
origins in $Z_g$ and the two positive fibers. Their entire installed
vectors coincide, but their three complete targets differ. On one vector
at most two entry states can produce at most two different correct rows,
which is impossible.

For the second assertion, the two queried right classes must be one
from each pair. If neither partner is queried, fix branch images at
those two right classes. An all-branch zero filling and positive
fillings at the two omitted right classes retain exactly those queried
values. The forced changes to the partners are unqueried. Fill their
remaining coordinates distinctly to obtain actual origins, again with
one installed vector and three different targets. Exterior-only Reads
have their common branch reply and cannot change either contradiction.
This proves both assertions for every depth or absence behavior of the
queried suffixes. $\square$

## 6. Arbitrary two-call readers force a whole constant positive fiber

**Theorem 6.1 (constant-positive-fiber theorem).**
Let the original prescribed $\sigma$ admit a correct arbitrary-literal
reader on every $u\in\mathcal U_*$, with at most nine installed states
and at most two actual calls per run. Then $\sigma$ is constant on at
least one entire $\Pi_j$.

Proof. Suppose for contradiction that all four positive fibers attain
both bits. The two faithful entries are distinct Reads, since each bit
occurs with four different positive targets. Lemma 4.1 leaves at most
four installed Reads. We classify these installed Reads, including
unused or redundant ones, by their queried classes. Words shorter than
three are exterior-constant Reads and have no queried class.

First suppose no class is queried by more than one Read. If some $b_j$
is unqueried, the first companion in Lemma 5.4 gives the output pair
$\{R_0,R_j\}$ on all of $\Pi_j$. Every variable branch coordinate
affects at most one Read. Lemma 5.3 makes the code constant on the entire
$\Pi_j$, a contradiction. Otherwise all four right classes are queried.
They exhaust the Read budget; there is no partner or exterior Read. If
any right-class suffix is nonempty, its partner is unqueried and the
second companion in Lemma 5.4 applies to that positive fiber. Lemma 5.3
again forces constancy. If all four suffixes are empty, this very table
is root-only, contradicting Theorem 4.2. This exhausts the case without
repeated queried classes, including any exterior or unused Reads that
fit in it.

Now suppose a class is queried more than once. Lemma 5.5 requires at
least three active classes: either at least three different right
classes, or two right classes and a partner. With at most four Reads,
there are therefore exactly four Reads in exactly three classes, with
multiplicities $2,1,1$. There is no exterior Read. Patterns $3,1$ or
$2,2$ leave only two active classes and violate Lemma 5.5; any further
active class with a repetition exceeds four Reads. There are exactly
five Halts, one unique $H_h$ with complete output $R_h$ for each
$0\le h\le4$.

If a partner $g$ is the repeated class, the two singly queried classes
must be one right class from each pair. Choose the omitted right index
$i$ in $g$'s pair. On $\Pi_i$ the two partner replies are fixed because
$x_g=\beta$. Its first zero companion supplies the two-entry output
pair, and every variable branch coordinate affects at most one of the
other Reads. Lemma 5.3 forces constancy on the entire $\Pi_i$.

It remains to consider a repeated right class $b_k$. If either of its
two suffixes is empty, choose an unqueried right index $i$. On $\Pi_i$
the value at $b_k$ is a branch image, so this root reply is constant.
Changing $b_k$ affects at most its other Read. Every other variable
coordinate is queried at most once, and the first zero companion for
$\Pi_i$ again gives constancy by Lemma 5.3.

We can therefore assume that both $b_k$ suffixes are nonempty. If its
partner $g(k)$ is unqueried, the second zero companion applies to
$\Pi_k$. Both repeated replies there are fixed absence at alpha; each
other variable coordinate affects at most one Read. Constancy on
$\Pi_k$ follows. This includes three distinct queried right classes
with no partner, and two right classes with a queried partner from the
opposite pair.

The only remaining configuration has two nonempty-suffix Reads
$A_0,A_1$ in $b_k$, one Read $G$ in its own partner $g=g(k)$, and one
Read $B$ in $b_l$ from the opposite pair. Write $\{k,i\}$ for the
right indices of $g$ and $\{l,j\}$ for the other pair. Thus $b_i,b_j$
and the other partner are unqueried. Write the two $A$ suffixes as
$w_0,w_1\ne\varepsilon$, the $G$ suffix as $v$, and the fixed $B$
suffix as $w_B$. We prove the contradiction for this entire remaining
configuration in four steps.

First, by the first companion, all vectors on $\Pi_i$ have entry-output
pair $\{R_0,R_i\}$, and all vectors on $\Pi_j$ have pair
$\{R_0,R_j\}$. Fix any $d\in\mathcal B$ at $b_k$. With this value
fixed, every other variable branch coordinate affects at most one Read.
The fresh-buffer lemma shows that the positive orientation throughout
the restricted $\Pi_i$ fiber depends only on $d$; call it $f_i(d)$.
The same argument on $\Pi_j$ gives $f_j(d)$. These statements include
all branch fillings, not just chosen samples.

Choose distinct $e,c\in\mathcal B$ avoiding $d$. There are actual
$\Pi_i$ and $\Pi_j$ fillings with $x_{b_k}=d$, $x_{b_l}=e$, and
$x_g$ respectively beta and $c$. Assign the required alpha in each,
assign its other partner as required, and fill the remaining unqueried
slots with fresh distinct branch images. Their installed reply vectors
differ at most at $G$. The two entry paths on the $\Pi_i$ vector are
disjoint, so one avoids $G$ and persists on the $\Pi_j$ vector. Its
output must belong to
$\{R_0,R_i\}\cap\{R_0,R_j\}=\{R_0\}$. The same entry is consequently
the zero entry in both contexts, and

$$
f_i(d)=f_j(d)=:f(d)\qquad(d\in\mathcal B).
\tag{NRN.13}
$$

Since $\Pi_i$ attains both bits, $f$ is nonconstant. Choose
$d_0,d_1\in\mathcal B$ with opposite orientations, and fix distinct
$e,c$ avoiding both. The preceding construction gives four actual
contexts, with $d=d_0$ or $d_1$ and $x_g=\beta$ or $c$. For each fixed
entry, changing $d$ changes its output between zero and the positive
target in each partner context. At the $d$ where that entry is positive,
changing the partner context changes its output from $R_i$ to $R_j$.
Both entries are known to terminate within two calls in all four contexts.

Second, neither entry can be $B$. At the fixed value $e$ its first
reply and successor are identical in all four contexts. For its output
to depend on $d$ within one remaining call, that successor must be
$A_0$ or $A_1$. A Halt is constant; $G$ depends only on the fixed
partner context; $B$ depends only on $e$. But a second call at an $A$
state depends only on $d$, so its resulting output is identical in the
two partner contexts. It cannot supply $R_i$ and $R_j$ at the $d$
where this entry is positive.

Neither entry can be $G$ either. In each fixed partner context, its
successor must be an $A$ state to distinguish $d_0,d_1$ in the last
call. The beta and $c$ contexts must select different $A$ states;
otherwise the positive output would be the same in both contexts.
The other distinct entry is neither a Halt nor $B$ nor this $G$, so
it is one of the two $A$ states. In one context the run from $G$
therefore visits this other entry as its second Read. The two running
paths meet on that fixed vector, contradicting Lemma 5.2 and their
different outputs. Hence the two entries are precisely $A_0,A_1$, in
one order.

Third, we determine all relevant $G$ successors, rather than just those
on the four contexts used to identify the entries. Take any
$d\in\mathcal B$ and choose compatible fresh $e,c$. The common positive
entry $f(d)$ is an $A$ state. Its first reply depends only on $d$,
but its output must change from $R_i$ to $R_j$ between the beta and
branch partner contexts. The only installed reply that can change is
at $G$. Within two calls its first successor must therefore be $G$,
and the second call forces

$$
\operatorname{next}(G,r_\beta(v))=H_i.
\tag{NRN.14}
$$

For every prescribed $c\in\mathcal B$, choose $d,e$ fresh and distinct
from $c$ and repeat this actual-source comparison. It forces

$$
\operatorname{next}(G,r_c(v))=H_j
                  \qquad\text{for every }c\in\mathcal B.
\tag{NRN.15}
$$

These successors really are Halts, since the second call exhausts the
bound; their uniqueness follows from the exact five-Halt count. If an
attainable branch reply equals $r_\beta(v)$, the two equations already
contradict the fixed table. In all cases in which the configuration
can persist, any second $G$ call at a beta partner returns $R_i$ and
any second $G$ call at a branch partner returns $R_j$. Neither is
$R_0$ or $R_k$.

Fourth, take any original source $u\in\Pi_k$. Its $b_k$ value is
alpha, its $g$ value is beta, and its $b_l$ value is a branch image.
Replace the first two values by beta and a fresh branch image,
respectively, keeping every other coordinate. The new injective
all-image filling gives an actual $u'\in Z_{b_k}$, with target $R_0$.
Both repeated partner occurrences are replaced together. Each $A$
reply is absent on both sources, since $w_0,w_1$ are nonempty and
both alpha and beta are leaves. The $B$ reply is identical. Thus
only $G$ can differ between their installed vectors.

Each actual correct execution starts at an $A$ entry and cannot visit
$G$: a visit within two calls would be second, and (NRN.14)–(NRN.15)
would return $R_i$ on $u$ or $R_j$ on $u'$, both incorrect. Each actual
correct path therefore avoids $G$ and persists, with the same output,
when started from that same entry on the other source. The two sources
cannot use the same entry, since their targets are $R_k$ and $R_0$.
They must use opposite bits. Their two correct $G$-free paths consequently
establish that on this arbitrary $\Pi_k$ source both entries terminate
within two calls with output pair $\{R_0,R_k\}$, and both paths avoid
$G$. In particular the entry not prescribed on $u$ has been justified
by a correct path on its actual zero companion.

Throughout the entire $\Pi_k$, the two $A$ replies are fixed absence
and the $G$ reply is its fixed beta reply. Only $B$ can vary with a
branch filling. Any two $\Pi_k$ vectors thus differ at at most one
Read and have the same two-entry output pair just proved. Lemma 5.2
forces the same positive orientation on every source in $\Pi_k$.
The original code is constant on this whole positive fiber, the final
contradiction.

All configurations of at most four installed Reads have now been
exhausted. Exterior, deep, absent, repeated, redundant and unused Reads
were included in that count and in the actual reply identities. The
argument permits early stopping, shared states and cycles in unions of
different-source paths. Therefore some entire positive fiber has
constant prescribed code. $\square$

## 7. Same-code normalization and the sharp four-call bound

**Theorem 7.1 (universal nine-state two-to-four normalization).**
For every lawful prescribed binary computation $\sigma$ in Assumption
3.1, existence of an arbitrary-literal reader with at most nine installed
states and at most two calls, correct on all of $\mathcal U_*$, implies
existence of a representative-root reader with nine installed states
and at most four calls, correct on every same actual origin with exactly
the original $\sigma(u)$.

Proof. Theorem 6.1 supplies $j,z$ with constancy on the whole $\Pi_j$.
Use the complete nine-state table and entries in Theorem 4.2. Its actual
right-root tests and stored entire rows give correctness on all eleven
profiles, hence on the whole actual domain. Acquisition and computation
of the code are unchanged: the producer exports exactly its originally
specified value. The alternative entry map has different entries for
different attained bits and retains no additional payload. All installed
states, all four successors and all running visits are charged as in
Definition 3.2. The theorem asserts existence of an alternative table;
it does not preserve the original reader's state names, paths, replies
or two-call bound. $\square$

**Corollary 7.2 (sharpness and the first failure of three calls).**
The universal four-call conclusion in Theorem 7.1 cannot be replaced by
three calls at the same state budget. Nine is the first installed-state
budget at which the corresponding two-to-three implication fails.

Proof. Directly apply NRE Theorem 8.6, Theorem 8.7 and Corollary 8.9
to their prescribed bit $\sigma^\dagger$ of NRE Definition 8.2. They
use exactly the finite sources (NRN.1), the full fiber (NRN.6), all five
whole rows of Definition 2.3 and the acquired-code, faithful-entry,
state-only stationary contract of §3. Corollary 8.9 supplies its
nine-state arbitrary-literal two-call realization and the first-failure
budget; Theorem 8.6 excludes every root competitor within nine states
and three calls; Theorem 8.7 gives its exact root call minimum four
at budget nine. These inherited proofs and their particular code are
not repeated as new content here. $\square$

**Remark 7.3 (unrestricted existence and bounded exclusions).**
Theorem 7.1 gives an affirmative unrestricted terminating root-existence
implication for every code in its premise, with the constructive cap
four. Theorem 4.2 gives the exact unrestricted criterion for all
prescribed binary codes in this model; its all-mixed complement has
the exact ten-state minimum of Theorem 4.3. Theorem 6.1 shows that this
complement cannot admit a nine-state arbitrary-literal two-call reader.

NRE's two-call and three-call exclusions remain exactly statements at
those call budgets. They supply no unrestricted nonexistence assertion.
The ten-state upper in Theorem 4.3 is a four-call construction for
all-mixed positive fibers; neither it nor Corollary 7.2 supplies
ten-state sufficiency at three calls. Unused states and duplicate-output
Halts cannot evade any lower bound, since they consume installed budget.

## 8. Acquisition and effective-extraction boundaries

**Convention 8.1 (comparison with the certificate-relative finite basis).**
The finite-basis results of PCA require their supplied valid determining
certificate: a finite actual native menu and its well-defined assignment
to the original complete entries. That hypothesis is stronger than
merely having a prescribed lawful acquired-term computation. The
permissions and preserved objects differ among the following results.

| PCA result | Certificate, design permission and preserved scope |
| --- | --- |
| Theorem 10.3 | Given the determining certificate, preparation literals can be restricted to its actual-address basis on exactly the same installed preparation states, partition, literal latches and common start. The original reader, whole outputs and entry map remain fixed. Preparation state/call/literal upper bounds and separately valid reader phase bounds are preserved. |
| Theorem 12.4 | Under that certificate, the finite paid word task is equivalent to original native preparation at identical preparation upper budgets and original reader entry. Its response table is mathematical task data; runtime still makes one paid native call at a Read. |
| Theorem 13.1 | With the reader immutable, the basis also includes its installed observations. One actual comparison origin then preserves that reader's path and charges while comparing the preparation, which supports correlated same-execution phase objectives. |
| Theorem 13.3 | Under the separate permission to redesign both running tables, the code-certificate basis suffices for the joint upper region, including same-execution objectives. The alphabets, partitions, preparation start, literal original entry values and whole-row Halt labels remain fixed. |

None of these results grants an arbitrary root-only reader, an unknown
profile-reading port, a silent control step or a free determining
certificate. Their selected actual witnesses retain the certificate's
original code. Theorem 7.1 instead deduces a constant-positive-fiber
property from a successful table at the specific nine-state/two-call
budget, and then installs the four-root chain with a possibly different
faithful entry map. It neither needs nor constructs a finite native menu
that generates the original code from a source-independent start. It
also preserves no preparation budget or correlated two-phase price.

**Convention 8.2 (finite acquired computation and paid generation differ).**
PCA Theorem 8.2 supplies a lawful acquired-term code served by its
fixed eight-state two-call reader but not generated by any finite
stationary fixed-address common-start preparer on the entire original
fiber, even with only sourcewise termination demanded. In its template,
the varying zero-fiber predicate asks whether an acquired branch image
contains an alpha leaf. Any proposed finite observing menu misses a
sufficiently deep actual alpha insertion, although full inspection of
each acquired finite term terminates. This is the cited acquisition
obstruction, not a new proof or a restriction to a finite source sample.

That code is within Theorem 7.1's post-entry existence premise. Its
root reader receives a bit that was genuinely computed on the supplied
acquired data and exported; root-reader existence does not generate
the bit for a preparer denied those data. Pre-entry acquisition,
acquired-term computation and workspace, code export, complete isolation,
lawful entry and stationary authentic service remain separate supplied
and paid operations, including when entry immediately reaches a Halt.

PCA Theorem 15.2 addresses extraction under explicit promises:
its programs are all total on acquired finite data and all their codes
are finitely preparable, with one unchanged eight-state reader and
complete entries. Nevertheless no effective procedure on every such
program returns a valid finite determining depth, determining menu or
finite common-start preparer for its original code. Its promise-preserving
halting reduction retains that scope. Theorems 4.2 and 7.1 contradict
none of these statements: once a constant pair $j,z$ is supplied, the
displayed root table is explicit, but the existence proof supplies no
uniform compiler extracting preparation, that pair or a determining
certificate from arbitrary acquired-code program text.

**Remark 8.3 (the precise source-replacement discipline).**
NBP Proposition 15.8 already refutes universal deep padding that
preserves an arbitrary prescribed code. No argument here assumes it.
The companions and fresh buffers of §5 are actual alternative origins
used to constrain one common successful table. Their codes may change;
correctness forces the opposite entry when their complete targets differ.
The remaining configuration in Theorem 6.1 proves validity of both
entries on every $\Pi_k$ vector before applying one-Read variation.
No statement about one selected source per profile is promoted to
constancy on a whole fiber without that argument or the actual-source
connectivity proof.

## 9. Suppliers, added content and remaining scope

**Convention 9.1 (mathematical ownership).**
The following separates the native premises, new structural deductions
and direct consequences.

| Result or supplier | Mathematical role |
| --- | --- |
| NBP Definitions 1.1–1.2 and 9.1; Propositions 9.3 and 15.2 | Finite ordered sources, literal rows, exact image inverse, every actual injective filling, all repeated occurrences and disequalities, eleven exhaustive profiles, infinite finite-branch supply, and the five complete predecessor outputs. |
| NBP Assumptions 9.2 and 10.6; Definitions 11.1 and 15.1; NRE Assumption 3.1 and Definition 3.2 | Acquired/exported prescribed code, complete access cut, faithful lawful entry, paid stationary native service, and the installed fixed-literal state-only contract. |
| NBP Proposition 12.5 and Theorem 15.4 | Per-source stationary no-revisit and the inherited eight-state same-code normalization. The latter enters the first-failure statement through NRE Corollary 8.9, not as a nine-state theorem. |
| Theorem 4.2 and §5 | New exact unrestricted root criterion, actual two-entry orientation and one-Read variation, actual fresh-buffer connectivity, zero companions and mandatory query classes. The graph and indistinguishability methods are elementary intermediates. |
| Theorem 6.1 | New exhaustive multiplicity proof of a whole constant positive fiber, including the universal $G$ successors and both $G$-free entry paths on every remaining $\Pi_k$ source. |
| Theorems 4.3 and 7.1 | Direct consequences with complete matching tables: the exact ten-state all-mixed root minimum and universal same-code nine-state four-call normalization. |
| NRE Theorems 8.6–8.7 and Corollary 8.9 | Inherited sharpness of four calls at budget nine and the first failure budget for two-to-three normalization. Their particular constructions and lower proofs are reused. |
| PCA Theorems 8.2, 10.3, 12.4, 13.1, 13.3 and 15.2 | The separate code-generation obstruction, certificate-relative finite bases with their stated reader permissions, and nonuniform extraction boundary. |

The new proofs use the named canonical native suppliers and ordinary
finite-state reasoning. No external theorem is imported as a premise
for their numerical or existence conclusions. No external-priority
claim or global literature-completeness claim follows from this bounded
source base. All new content is `repo-derived` ordinary mathematics.

**Convention 9.2 (remaining mathematical and realization limits).**
The unrestricted nine-state root implication in this precise model is
settled by Theorem 7.1, and the all-code root criterion is Theorem 4.2.
These do not classify all arbitrary-literal two-call compatible codes,
decide compatibility of an arbitrary supplied code computation, or
classify arbitrary-call arbitrary-literal readers and other state
budgets. Changed cuts, source promises, extra updates, extra source
ports, source-bearing entry fields, randomization, computed addresses
and additional workspace require their own correspondence and proofs.

The finite tables price every installed abstract state and every native
running visit. They supply no total physical storage, elapsed-time,
energy, address-weighted optimum, acquisition cost, producer workspace
or service implementation theorem. Address and successor-table storage,
fixed whole-output storage, installation, transition work and literal
submission retain their separate prices. Neither an inverse witness
nor a row equality authenticates a physical register or supplies an
inverse update. Acquisition, actual export, complete isolation, faithful
entry after absorbing stop and authentic stationary service remain
premises. There is no kernel-verification, empirical machine-learning,
physical-resource, worldwide-originality or overall-programme completion
claim.

[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[NRE]: FIB_PRESCRIBED_CODE_NINE_STATE_ROOT_ESCAPE.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md

## 追加锚（本行以下为增补区）
