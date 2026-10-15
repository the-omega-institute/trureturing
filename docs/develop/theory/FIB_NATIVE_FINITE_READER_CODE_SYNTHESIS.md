# Finite-reader compatibility and lawful binary-code synthesis

> This is an append-only `generic-v1` reference volume. Its locators are
> determined by its own Markdown bytes. Corrections and extensions belong
> in numbered sections after the final append anchor, preserving the
> existing text.

For an arbitrary explicit finite stationary reader table, two fixed
faithful labeled entries and a finite call bound, this volume decides
whether some lawful acquired-term code attaining both original bits makes
that unchanged reader correct on the entire repeated-partner inverse
fiber. A positive answer specifies such a code without assuming an
existing compatible code. Exact actual profile multiplicities also give
the labels that can occur at each source in some compatible code.

The canonical suppliers are [Native cut-birth provenance and literal
past-row recovery][NBP] (NBP), [Native prescribed-code acquisition on the
original one-image fiber][PCA] (PCA), and [Table-driven common root
normalization for prescribed binary codes][TCR] (TCR). Native objects,
whole outputs and exact prefix attainment are inherited. The additional
results are their multiplicity, surjective-selection and lawful synthesis
consequences, together with a fixed-table verification separation.

This is `repo-derived` ordinary paper mathematics. It is reference input,
not a Lean truth source or kernel certificate. The finite procedures are
mathematical specifications; no mathematical algorithm, enumeration,
experiment, test or build is executed as evidence here. No worldwide
originality, efficiency or physical realization claim is made.

## 1. The entire native inverse fiber

**Definition 1.1 (finite trees, update and actual replies).** The sources
are all finite nonempty ordered terms

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{FCS.1}
$$

Native Boolean true and false name alpha and beta; the false and true
address letters name $L$ and $R$. These conventions do not relabel the
exported bits $0,1$. Every word in $\mathcal W=\{L,R\}^{*}$, including
$\varepsilon$, is a legal query. The truthful reply $r_t(v)$ is the
constructor alpha, beta or $\mathsf{branch}$ at a reached node, and
$\mathsf{absent}$ outside the finite tree. Every nonempty continuation
at a leaf is absent. At any existing occurrence $p$,

$$
r_t(pw)=r_{t|_p}(w)\qquad(w\in\mathcal W).
\tag{FCS.2}
$$

Equality retains brackets, order and both leaf labels. Equal subtrees at
different addresses remain different occurrences. These are NBP
Definitions 1.1–1.2 and TCR Definition 2.1's original objects.

**Definition 1.2 (complete canonical row).** For a finite prefix-free cut
$P$, let $H_P(t)=P\cap\operatorname{Pos}(t)$. Replace the whole subtree
at each reached $p\in H_P(t)$ by its occurrence hole $\square_p$, retaining
every other exterior bracket and concrete leaf. The complete row is
$R_P(t)=(C_P(t),\pi_P(t))$, where

$$
p\sim_{\pi_P(t)}q\quad\Longleftrightarrow\quad t|_p=t|_q.
\tag{FCS.3}
$$

Every two different blocks assert disequality. An unreached cut has its
concrete strict-prefix blocking leaf in the exterior. Order reached holes
lexicographically, and name a class by the zero-based position of its
first member. Recompute names after restriction; the occurring names
need not be consecutive. A tuple indexed by classes indexes the occurring
names, not an assumed consecutive list of raw ordinals.

**Definition 1.3 (fixed repeated partners and full domain).** Fix
$P=\{L,R\}^{3}$ and its perfect depth-three exterior $C_*$. Its complete
partition $\pi_*$ has the six classes below. The aliases denote canonical
classes, not acquired values.

| Alias | Representative $p_d$ | All occurrence holes |
| --- | --- | --- |
| $a$ | $LLL$ | $LLL,LRL$ |
| $c$ | $RLL$ | $RLL,RRL$ |
| $b_1$ | $LLR$ | $LLR$ |
| $b_2$ | $LRR$ | $LRR$ |
| $b_3$ | $RLR$ | $RLR$ |
| $b_4$ | $RRR$ | $RRR$ |

Put $D=\{a,c,b_1,b_2,b_3,b_4\}$ and $R_*=(C_*,\pi_*)$. For class
values $x:D\to\mathcal T$ write

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{FCS.4}
$$

The domain and target throughout are exactly

$$
\mathcal U_*=
 \{u\in\mathcal T:R_P(\rho u)=R_*\},\qquad
t_u=\rho u,\qquad F(u)=R_P(u).
\tag{FCS.5}
$$

Every compatible finite origin is included. There is no source-size,
depth, rank, selected-family or additional history promise. Both
occurrences of each partner use the same value, and all six different
classes are pairwise disequal.

**Proposition 1.4 (inherited actual image classification).** Let
$\mathcal I=\rho[\mathcal T]$. Its disjoint grammar and inverse are

$$
\begin{aligned}
\mathcal I&::=\beta\mid E\mid\langle\mathcal I,\mathcal I\rangle,\\
\delta(\beta)&=\alpha,\qquad \delta(E)=\beta,\\
\delta\langle y,z\rangle&=\langle\delta y,\delta z\rangle
                                      \quad(y,z\in\mathcal I).
\end{aligned}
\tag{FCS.6}
$$

Writing $\mathcal B=\mathcal I\setminus\{\beta\}$ for the branch
images, the eleven cases in this table are nonempty, disjoint and
exhaust $\mathcal U_*$. In every row all different class values remain
disequal; the unspecified values range over every allowed finite branch
image.

| Actual case | Forced leaves | Other class values | Whole target |
| --- | --- | --- | --- |
| $\Pi_1$ | $x_a=\beta,\ x_{b_1}=\alpha$ | Four distinct branch images | $R_1$ |
| $\Pi_2$ | $x_a=\beta,\ x_{b_2}=\alpha$ | Four distinct branch images | $R_2$ |
| $\Pi_3$ | $x_c=\beta,\ x_{b_3}=\alpha$ | Four distinct branch images | $R_3$ |
| $\Pi_4$ | $x_c=\beta,\ x_{b_4}=\alpha$ | Four distinct branch images | $R_4$ |
| $Z_a$ | $x_a=\beta$ | Five distinct branch images | $R_0$ |
| $Z_c$ | $x_c=\beta$ | Five distinct branch images | $R_0$ |
| $Z_{b_1}$ | $x_{b_1}=\beta$ | Five distinct branch images | $R_0$ |
| $Z_{b_2}$ | $x_{b_2}=\beta$ | Five distinct branch images | $R_0$ |
| $Z_{b_3}$ | $x_{b_3}=\beta$ | Five distinct branch images | $R_0$ |
| $Z_{b_4}$ | $x_{b_4}=\beta$ | Five distinct branch images | $R_0$ |
| $Z_*$ | None | Six distinct branch images | $R_0$ |

Precisely all injective valuations with $\mathscr S(x)\in\mathcal I$
occur, with the bijection

$$
x\longmapsto\delta(\mathscr S(x)),\qquad
u\longmapsto x_d=t_u|_{p_d}.
\tag{FCS.7}
$$

Proof. These are NBP Proposition 9.3, Proposition 15.2 and Theorem 10.4,
also recorded in PCA Definition 4.1 and TCR Supplier 2.4. The following
direct image argument fixes the conditions used here. Each source
constructor gives one case of (FCS.6), and each image case has the stated
preimage. Alpha is not an image; $E$ is not a pair of images because its
right child is alpha. Hence the cases are disjoint. Recursion decreases
finite size, and structural induction gives $\delta\rho=\mathrm{id}$
and $\rho\delta=\mathrm{id}$ on their domains. In particular $\rho$
is injective. The same image grammar shows that every subtree of an
image is either alpha or an image; every branch subtree is an image.

In $\mathscr S(x)$ the root and its two depth-one children have branch
right children, so none can be $E$. Each depth-two block must therefore
be either $E$, forcing its right value alpha and its left partner beta,
or a pair of image values. The four right classes are different, so at
most one is alpha. Conversely these alternatives make all four blocks,
and then the whole filling, images. The legal injective row filling has
exactly $R_*$, including repetitions and every disequality; its inverse
is an actual finite origin. Extracting representative subtrees recovers
the valuation, proving (FCS.7).

Beta is the only image leaf. With an alpha right class its forced beta
partner precludes beta in any other class; without alpha there is at
most one beta class. This gives exactly the eleven root cases. For
explicit fresh branch images put

$$
B_0=\beta,\qquad B_{n+1}=\langle B_n,B_n\rangle.
\tag{FCS.8}
$$

For $n\ge1$ these are branch images with every leaf at depth $n$.
Their different heights make them distinct. Choosing finitely many
different such images realizes each case and avoids any finite forbidden
list. Every permitted filling, not just these witnesses, has its actual
origin by (FCS.7). The target assertions are the complete-row calculation
in §2. $\square$

## 2. All five whole predecessor outputs

**Definition 2.1 (literal exteriors and complete partitions).** Write
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$. The complete rows
$R_h=(C_h,\pi_h)$ are as follows:

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
\tag{FCS.9}
$$

$$
\begin{aligned}
\pi_0&=\{\{LLL,LRL\},\{LLR\},\{LRR\},
                    \{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_1&=\{\{LRL\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_2&=\{\{LLL\},\{LLR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_3&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RRL\},\{RRR\}\},\\
\pi_4&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL\},\{RLR\}\}.
\end{aligned}
\tag{FCS.10}
$$

Every pair of different blocks in each partition asserts disequality.
The remaining canonical data are part of the output as well.

| Row | Ordered reached holes | Recomputed name vector | Absent cut members and concrete guard |
| --- | --- | --- | --- |
| $R_0=R_*$ | $LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,0,3,4,5,4,7)$ | None |
| $R_1$ | $LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LLL,LLR$; beta at $LL$ |
| $R_2$ | $LLL,LLR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LRL,LRR$; beta at $LR$ |
| $R_3$ | $LLL,LLR,LRL,LRR,RRL,RRR$ | $(0,1,0,3,4,5)$ | $RLL,RLR$; beta at $RL$ |
| $R_4$ | $LLL,LLR,LRL,LRR,RLL,RLR$ | $(0,1,0,3,4,5)$ | $RRL,RRR$; beta at $RR$ |

**Proposition 2.2 (whole-row target, with occurrence-sensitive repair).**
On $\Pi_j$ the target is exactly $R_j$; on every $Z_d,Z_*$ it is exactly
$R_0$. The five rows are different.

Proof. Apply the inherited inverse and NBP Proposition 9.3's
occurrence-sensitive predecessor calculation. In a zero case all six
values are images. Each depth-two block is a pair of images, so its
predecessor is an old pair with both cut occurrences still present.
All eight holes remain, and injectivity of $\rho$ preserves their entire
equality and disequality partition. This gives $R_0$.

On $\Pi_j$ exactly block $q_j$ is $E$. Its predecessor is the concrete
beta leaf; its two current children are newborn and were absent before
the update. The other three blocks are pairs of images. Consequently
exactly those two holes disappear, giving $C_j$ and the restriction of
$\pi_*$ to the other six occurrences. Injectivity preserves all their
equalities and disequalities. Reordering those holes and taking their
first-member positions gives precisely the vectors above. The beta at
$q_j$ is the strict-prefix guard for the two absent cuts. When the
partner is repeated, its occurrence in the other block remains an old
hole, even though its current value is beta. Classwise removal would
give a different row. Finally the five reached supports are different,
so the rows are pairwise different. $\square$

## 3. Supplied services and the arbitrary finite reader

**Assumption 3.1 (acquisition, export, isolation and paid service).**
Exactly one genuine authenticated update binds the actual origin $u$
to the same register $t_u=\rho u$. The origin, root, cut and version
are fixed, with no resets, rerooting, source substitution, arbitrary
edits or subsequent updates. Authentication certifies continuity and
selects no source within $\mathcal U_*$. The complete current row is
lawfully acquired on that stationary version.

Before the access cut a producer genuinely possesses same-source,
same-version finite data $A(u)$: either the lossless current tree, or
$R_*$ and one acquired finite subtree value for each of the six classes.
Local structural inspection and equality comparison act on those acquired
terms. A lawful code is computed by a terminating finite deterministic
computation on those data. The producer actually exports its complete
original bit with the row before access to the acquired material is lost.

A supplied lawful common entry exposes exactly that bit, $P,R_*$ and
common source-independent controls, with the declared payload recoverable
at entry. No additional source-bearing identifier, predecessor data,
alpha marker, acquired value, old output, trace, cache, archive, pointer,
allocation, control field, acquisition order or count, length, meter,
timing or update packet is accessible. A field determined by the payload
adds no distinction; any further field changes this contract. Material
made inaccessible need not be physically erased.

The same current register stays stationary during reading. Its sole
source port is the native literal four-reply port. There is no
unknown-subtree equality, image, provenance, generation, inverse or
additional subtree port. Every invocation counts, including repeats,
absences, leaf continuations and addresses previously used in acquisition.
Acquisition, local acquired-term computation, constants, workspace,
authentication, installation, representation, actual export, isolation,
faithful lawful entry and continuing authentic stationary service are
separately supplied and priced. An absorbing producer stop supplies no
resume action; later entry is a separately supplied invocation. These
are NBP Assumption 9.2 and PCA Assumption 1.2's acquired-data route,
with the complete services retained as in TCR Assumption 3.1.

**Definition 3.2 (explicit installed table and original entries).** Fix
any finite Moore table $T$ on a disjoint installed set $\mathcal K=Q\sqcup H$,
with

$$
\operatorname{addr}:Q\to\mathcal W,\qquad
\operatorname{next}:Q\times\mathcal A\to\mathcal K,\qquad
\operatorname{out}:H\to\mathcal R_P,
\quad
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}.
\tag{FCS.11}
$$

Here $\mathcal R_P$ is the set of complete canonical rows at $P$.
Fix distinct labeled states $e_0,e_1\in\mathcal K$; entry for the
original bit $z$ is exactly $e_z$, with its fixed inverse labeling.
A Read state makes one actual call at its fixed finite literal and
takes the successor for its reply. A Halt returns its fixed entire
row without a call. Every installed state counts, including unused
Reads, unused Halts and different Halts with the same output. All four
successors at every Read remain installed. The input includes all states,
addresses, transitions, outputs and the two entry labels.

After entry the current state is the whole accessible mutable
source-dependent memory. There is no extra bit, reply or address register,
computed address, independent program counter, phase, clock, history,
archive, source-dependent table selector, output decoder or free control
transition. Shared states, repeated literals, early Halts, convergence
and cycles are allowed. Nothing restricts $|\mathcal K|$ to nine or
the call bound to two. The table and labeled entries remain unchanged
throughout synthesis.

**Definition 3.3 (lawful BOTH-bit-attained compatibility).** For any
$L\in\mathbb N_0$, let $\mathcal C_L(T)$ consist of codes
$\sigma:\mathcal U_*\to\{0,1\}$ realized by a specified total finite
deterministic acquired-term computation under Assumption 3.1, actually
exported there, such that

$$
\sigma[\mathcal U_*]=\{0,1\},\qquad
\forall u\in\mathcal U_*,\quad
T\text{ from }e_{\sigma(u)}\text{ returns the whole }F(u)
\text{ within }L\text{ calls}.
\tag{FCS.12}
$$

There is no additional bound on the producer's finite computation,
constants or workspace. Arbitrary extensional functions are not presumed
lawful: sufficiency below constructs a finite computational realizer.
Only the selected entry must be correct and terminate on a source.
The other entry may return a wrong row, exceed the bound or diverge.
No compatible initial code, determining certificate, source oracle or
denied archive is an input.

## 4. Exhaustive actual profiles and exact cell multiplicities

**Definition 4.1 (inclusive profiles of the entire installed menu).** Put

$$
b=\max\bigl(\{0\}\cup
 \{|\operatorname{addr}(q)|-3:q\in Q,\ |\operatorname{addr}(q)|\ge3\}\bigr).
\tag{FCS.13}
$$

This uses every installed Read, including unused states, repeated words
and words visited only from an incorrect entry. It bounds observations
of this finite table and imposes no bound on actual sources.

At each class $d$, enumerate prefix patterns through inclusive relative
depth $b$. At a reached node before the frontier choose alpha, beta,
or an ordered pair of recursively smaller patterns. A leaf is retained
literally and stops descent; every strict descendant is absent. At depth
$b$ choose alpha, beta, or a live name $z_{d,w}$ recording a branch
at that relative occurrence. A live name must be filled by a branch
image. This is a bounded recursion with three possibilities at remaining
depth zero and two leaves or a pair at positive remaining depth.

Let $A_d$ be the resulting free ordered term. Different pairs $(d,w)$
have independent names, without a requirement that their values differ.
Every occurrence of class $d$ in $C_*$ uses the same whole $A_d$ and
the same names. The negatives are exactly

$$
\Delta=\bigwedge_{d\ne e} A_d\ne A_e.
\tag{FCS.14}
$$

They concern whole class terms, including all fixed ground pieces.
Expand grounds literally in the ordered alpha/beta signature for syntax
tests. Define

$$
\begin{aligned}
J(\alpha)&=\mathsf{false},&J(\beta)&=\mathsf{true},&J(z)&=\mathsf{true},\\
J(\langle A,B\rangle)
&\Longleftrightarrow
 (A\text{ is literally }\beta\ \land\ B\text{ is literally }\alpha)
 \ \lor\ (J(A)\land J(B)).
\end{aligned}
\tag{FCS.15}
$$

Retain precisely the pattern tuples satisfying

$$
J(\mathscr S(A))\quad\land\quad
\forall d\ne e,\ A_d\text{ and }A_e\text{ have unequal free syntax}.
\tag{FCS.16}
$$

Denote this finite family by $\Omega_b$. It is PCA Definition 11.1's
profile family at relative depth $b$ and on the row of Definition 1.3;
it is also TCR Definition 5.1's family for this installed menu.
PCA's $T_d,J,\Delta$ are respectively our $A_d,J,\Delta$. Neither
the profile definition nor its attainment requires a code-determining
assignment. Write $\eta_b(u)$ for the actual profile of $u$ and
$\mathcal U_\eta=\{u\in\mathcal U_*:\eta_b(u)=\eta\}$.

**Lemma 4.2 (the simultaneous filling calculation for these profiles).**
For a retained tuple, all its whole-class negatives can be satisfied
simultaneously by finite branch-image fillings of its live names. For
any finite $M\ge0$ they can all have minimum leaf depth greater than
$M$, while every closed piece stays literal.

Proof. This is the elementary height-tag filling of TCR Lemma 5.2,
used for PCA Theorem 11.2's exact attainment. Here are its needed
details. Let $h\ge1$ bound the heights of the six free terms, treating
names as leaves. List the live names as $z_1,\ldots,z_n$ and use the
all-beta images (FCS.8). Set

$$
N_i=\max\{h,M\}+1+i(h+1),\qquad z_i\longmapsto B_{N_i}
\quad(1\le i\le n).
\tag{FCS.17}
$$

The heights $N_i$ exceed $h,M$ and have gaps greater than $h$.
Induction on a free term shows that its evaluated height is the maximum
of its concrete-leaf depths and the numbers $N_i+$ the depths of its
occurrences of $z_i$.

For different free terms descend through equal ordered pair constructors
to a first syntactic mismatch. Different concrete constructors stay
different; different names have different assigned heights. For a name
$z_i$ against a nonvariable subterm $A$, a ground $A$ has height at
most $h<N_i$. Otherwise let $N_j$ be the largest assigned height among
names occurring in $A$. If $N_j<N_i$, the evaluated height of $A$ is
at most $\max\{h,N_j+h\}<N_i$. If $N_j>N_i$, it is at least
$N_j>N_i$. If $N_j=N_i$, that name occurs at positive depth in the
nonvariable $A$, whose evaluated height is then greater than $N_i$.
These cases exclude equality at every possible mismatch. Injectivity
of the pair constructor carries the distinction back to the original
terms. Thus one assignment satisfies every syntactically nontrivial
whole-class negative, including negatives against closed ground classes.

Each assigned value is a finite branch image with minimum leaf depth
$N_i>M$. Only genuine frontier branches are replaced. An early leaf,
its absent cone, or a fully exposed $E$ stays literal. If there are no
live names the empty assignment suffices for the already unequal ground
terms. This is the needed specialization, not a new general filling or
prescribed-rank theorem. $\square$

**Proposition 4.3 (exact actual attainment and coverage).** One has

$$
\Omega_b=\{\eta_b(u):u\in\mathcal U_*\}.
\tag{FCS.18}
$$

In particular the nonempty cells $\mathcal U_\eta$ partition exactly
the original actual domain. Every retained tuple has an explicitly
constructed finite current filling and its actual inverse origin.

Proof. Under any assignment of branch images to live names, $J$ is
exact for image membership of the evaluated free term. Literal and name
cases follow from (FCS.6). At a pair, becoming $E$ requires both children
literally beta and alpha: neither a name, filled by a branch, nor a pair
can become a leaf. The other image alternative is exactly a pair of
images. Induction proves exactness of (FCS.15), also at $\mathscr S(A)$.

An actual source has a unique inclusive prefix decomposition with stops
at its early leaves. Every live frontier branch is an image, by
Proposition 1.4's subtree fact. Its assignment therefore passes $J$.
Identical free class terms would evaluate equally and violate an actual
whole-class disequality. Thus every actual profile passes (FCS.16).

Conversely take a retained tuple and apply Lemma 4.2 to all of (FCS.14)
at once. The six resulting values $x_d$ are pairwise different, and
exactness of $J$ puts $\mathscr S(x)$ in $\mathcal I$. The bijection
(FCS.7) gives the finite actual origin $\delta(\mathscr S(x))$ with
exactly the original complete current row. Its prefix is exactly the
retained tuple: the fixed constructors remain, all live values are
branches, and no value is filled below a recorded leaf. Repeated
partners share the same class term throughout. Thus every retained cell
is actual, and none is omitted. This is PCA Theorem 11.2 and TCR
Proposition 5.3 at the precise parameters above, with the filling details
exposed. $\square$

**Theorem 4.4 (exact actual multiplicities).** Define

$$
m_\eta=
\begin{cases}
1,&\eta\text{ has no live name},\\
\aleph_0,&\eta\text{ has at least one live name}.
\end{cases}
\qquad |\mathcal U_\eta|=m_\eta.
\tag{FCS.19}
$$

Proof. A closed profile fixes every whole class value as a finite ground
term. Its whole current filling is fixed and has a unique inverse, so
the actual cell is a singleton. For a live profile, replace each $N_i$
in (FCS.17) by $N_i+k$ for $k=0,1,2,\ldots$. All gaps and lower
bounds used in Lemma 4.2 persist. Every assignment still satisfies the
whole-class negatives and image test and has the identical exposed
profile. At any one fixed live occurrence its inserted subtree height
strictly increases. Hence the class tuples, current trees and inverse
origins are all different. This supplies countably many actual points,
including two explicit distinct ones at $k=0,1$. All finite ordered
alpha/beta terms form a countable set, giving the reverse cardinal
bound. Thus a live cell is exactly countably infinite. $\square$

## 5. Finite good-entry data for every installed state

**Definition 5.1 (complete replies, targets and bounded paths).** For
$\eta\in\Omega_b$, let $v_\eta(q)$ be the actual reply at
$\operatorname{addr}(q)$ specified by its patterns. A word shorter
than three reads a common exterior branch. Any other installed word
has the unique form $pw$, $p\in P$, with $|w|\le b$ and reply that
of class $[p]$ at $w$. The pattern gives that reply, including every
absence after an early leaf. Both partner occurrences, repeated words
and unused states are included. The class roots give its unique case
of Proposition 1.4 and hence its entire target $F_\eta=R_{h(\eta)}$.

For each original label $z$ start at $e_z$ with zero calls. Inspect a
Halt before attempting any call, accepting it exactly when its complete
output equals $F_\eta$. At a Read with fewer than $L$ calls used,
take its successor for $v_\eta(q)$ and add one call. Inspect the
successor again, also immediately after the $L$th call. A wrong Halt
fails, and a Read still present at the limit fails. Let

$$
G_\eta=\{z\in\{0,1\}:\text{this bounded path accepts}\}.
\tag{FCS.20}
$$

Whole-row comparison includes the finite exterior, complete partition,
recomputed canonical names, every disequality and every blocking guard.
An output outside the five required whole rows is not accepted by
comparing only a label. At $L=0$ only an initial correct Halt accepts.
This is TCR Definition 6.1's bounded path test with its bound two replaced
by the arbitrary input $L$.

**Lemma 5.2 (exactness on every actual point).** For every
$u\in\mathcal U_\eta$,

$$
G_\eta=
\{z:T\text{ from }e_z\text{ on stationary }t_u
       \text{ returns the whole }F(u)\text{ within }L\text{ calls}\}.
\tag{FCS.21}
$$

Proof. Equation (FCS.2) and the definition of $b$ fix the reply of
every installed Read on every member of the cell. Proposition 2.2 fixes
its entire target. Induction from either identical entry makes the
bounded and actual paths have identical states, one paid invocation at
each Read, and identical outputs at a Halt. The last successor is
inspected in both contracts, so a Halt just after the last call succeeds
and a still-running state does not. Initial Halts and wrong early
outputs are likewise identical. A cycle or a longer unfinished run
simply fails that entry's bounded test. No termination or correctness
condition on the other entry was used. $\square$

## 6. Exact existence, lawful synthesis and extendible labels

**Theorem 6.1 (promise-free finite criterion and SOME-code synthesis).**
For every explicit finite $T$, its fixed distinct labeled entries and
every $L\in\mathbb N_0$, one has $\mathcal C_L(T)\ne\varnothing$
if and only if both conditions hold:

$$
\begin{aligned}
\mathrm{(A)}\quad&\forall\eta\in\Omega_b,\quad G_\eta\ne\varnothing;\\
\mathrm{(B)}\quad&\exists\eta_0,\eta_1\in\Omega_b,\quad
0\in G_{\eta_0},\quad 1\in G_{\eta_1},\quad
\bigl(\eta_0\ne\eta_1\ \lor\ m_{\eta_0}\ge2\bigr).
\end{aligned}
\tag{FCS.22}
$$

These are finite decidable conditions. When they hold a terminating
finite mathematical construction specifies a total lawful acquired-term
code with actual range exactly $\{0,1\}$ for the unchanged table and
entries, without a supplied compatible code.

Proof of necessity. Let $\sigma\in\mathcal C_L(T)$. Every retained
cell is actual by Proposition 4.3. At each of its points Lemma 5.2 puts
$\sigma(u)$ in $G_\eta$, proving (A). Both bits are attained, so
choose $u_0,u_1$ with values $0,1$. They are different source points.
Their cells allow the respective bits. If their profiles differ, (B)
holds by its first alternative. If they agree, that cell contains two
different points; Theorem 4.4 excludes a closed singleton, proving its
second alternative. A single source cannot supply both values of a
function.

Proof of sufficiency and lawfulness. Fix an order of finite patterns
and select the first passing ordered pair in (B). For different cells,
Lemma 4.2 supplies one ground tuple $X^0,X^1$ in each. Their profiles
make them different. For one common live cell use the $k=0,1$ tuples
from Theorem 4.4. In either case their actual inverse origins
$u_0,u_1$ are distinct, with $z\in G_{\eta_z}$ for $z=0,1$.
The inverse origins certify actual attainment; runtime stores their
six finite current class values, not an origin oracle.

For each retained profile store $a_\eta=\min G_\eta$. On genuinely
acquired input, extract its six class terms by finite local descent if
the lossless current tree is supplied. Use the fixed public class
indexing, and compute

$$
\widehat\sigma(x)=
\begin{cases}
0,&x=X^0,\\
1,&x=X^1,\\
a_{\eta_b(x)},&\text{otherwise}.
\end{cases}
\tag{FCS.23}
$$

The two tuple tests are disjoint. Equality of finite ordered terms is
decided by structural recursion: equal leaf constructors match, pairs
require both children to match, and different constructors fail. Prefix
extraction is bounded finite descent with literal leaf stopping; lookup
uses the finite stored profile table. All these computations terminate
on finite acquired terms. A representation check and fixed fallback bit
on malformed or nonretained finite inputs make the program total there
as well. On every supplied actual input its profile is retained, so
the fallback is unused. No operation queries an unknown subtree,
consults a source oracle, reads a denied archive or invokes an equality
port.

An entire class tuple determines $\mathscr S(x)$ and, by injectivity
of $\rho$, its unique origin. Thus the exceptions occur exactly at
$u_0,u_1$, and both original bits are actually attained. At each exception
the selected bit is good on its cell. Everywhere else the nonempty-set
default is good. Lemma 5.2 proves correct whole output within $L$ calls
on every original source from exactly $e_{\widehat\sigma(u)}$.
Assumption 3.1 supplies the actual export and faithful entry for this
computed bit. The table, its labels, outputs, states and transitions
are unchanged.

Finally, (FCS.13) is finite, the pattern recursion is bounded, and
(FCS.15) and whole-term syntax equality are finite structural tests.
There are two bounded paths per retained profile and finitely many
ordered profile pairs. Closed/live multiplicities are read from syntax;
the ground witness rule and the encoder specification are finite.
Consequently decision and emission terminate. No initial $\sigma_0$
was assumed. Agreement between extensional feasibility and lawful
feasibility is a conclusion of the explicit computation (FCS.23), not
a replacement of the lawful code class by all functions. $\square$

**Theorem 6.2 (exact pointwise extendible labels).** Fix any actual
$u\in\mathcal U_\eta$. A bit $z$ equals $\sigma(u)$ for some
$\sigma\in\mathcal C_L(T)$ if and only if

$$
\mathrm{(A)},\qquad z\in G_\eta,\qquad
\exists\xi\in\Omega_b,\quad
1-z\in G_\xi,\quad
\bigl(\xi\ne\eta\ \lor\ m_\eta\ge2\bigr).
\tag{FCS.24}
$$

Thus the exact extendible-label set is computable from the finite data
and is the same for all points of one cell.

Proof. A compatible code gives (A) and its selected bit is good. Its
opposite bit must occur at a different actual point $v$. The cell of
$v$ either differs from $\eta$ or contains at least two points. This
gives necessity by Theorem 4.4.

Conversely assume (FCS.24). If $\xi\ne\eta$, any constructed point
of $\mathcal U_\xi$ differs from $u$. If $\xi=\eta$ is live, the
two explicit fillings from Theorem 4.4 ensure that at least one differs
from $u$; take it as $v$. Store the finite actual current tuples of
$u,v$, assign $z,1-z$ at them and use $\min G$ elsewhere. The same
finite acquired-term comparison and profile lookup as (FCS.23) are lawful,
correct and both-attained. They realize the desired value at $u$.
This is existence for the specified finite point, with its finite tuple
as a constant, and asserts no free acquisition of an unknown $u$.
The condition depends on a cell only through its good sets and exact
multiplicity, proving the final assertion. $\square$

**Convention 6.3 (producer charges).** The finite inventory, default-bit
lookup, two entire ground tuples, fixed code and any reconstruction
workspace are producer resources. Their size can depend on $T,L$ and
the chosen witnesses. The theorem gives no useful uniform size or time
bound and does not charge them as if they were installed reader states.
The producer already has the acquired terms under Assumption 3.1.
Acquiring them, computing the bit, storing constants, exporting it,
isolating other material and entering the reader remain separate paid
operations. A finite table criterion supplies none of those services.

## 7. An actual good label that is not extendible

**Proposition 7.1 (a closed singleton can force its only code value).**
There is an explicit finite reader on the same entire $\mathcal U_*$,
with distinct fixed labeled entries and finite $L$, for which both bits
are good at one actual source but one of those good labels occurs there
in no member of $\mathcal C_L(T)$.

Proof. Use the concrete branch images $B_n$ of (FCS.8) and fix the tuple

$$
X^*=(x_a,x_c,x_{b_1},x_{b_2},x_{b_3},x_{b_4})
    =(B_1,B_2,B_3,B_4,B_5,B_6).
\tag{FCS.25}
$$

These six values are distinct branch images. Hence
$t^*=\mathscr S(X^*)$ has the actual inverse $u^*=\delta(t^*)\in Z_*$,
with whole target $R_0$. Let $n_a=1,n_c=2,n_{b_1}=3,n_{b_2}=4,
n_{b_3}=5,n_{b_4}=6$. Its exact node-address set is the finite set

$$
\mathcal N=\{v:|v|<3\}\ \cup\
 \bigcup_{p\in P}\{pw:|w|\le n_{[p]}\}.
\tag{FCS.26}
$$

Order it first by length and then lexicographically as
$v_1,\ldots,v_N$. Its expected constructor $c_i$ is branch at
$|v_i|<3$, branch at $v_i=pw$ with $|w|<n_{[p]}$, and beta when
$|w|=n_{[p]}$. Thus (FCS.25)–(FCS.26) specify every test and its
expected reply without an unknown-source parameter.

Install disjoint Reads $A_1,\ldots,A_4,D_1,\ldots,D_N,D_\infty$
and the five Halts $H_0,\ldots,H_4$ storing the whole rows of §2.
The following formulas specify all four successors at every Read:

| Read | Fixed literal | Successor for every $r\in\mathcal A$ |
| --- | --- | --- |
| $A_j$, $1\le j\le4$ | $p_{b_j}$ | $H_j$ if $r=\alpha$; otherwise $A_{j+1}$ if $j<4$, and $H_0$ if $j=4$ |
| $D_i$, $1\le i\le N$ | $v_i$ | $D_{i+1}$ if $r=c_i$ and $i<N$; $H_0$ if $r=c_i$ and $i=N$; $D_\infty$ otherwise |
| $D_\infty$ | $\varepsilon$ | $D_\infty$ for every reply |

Take $e_0=A_1$, $e_1=D_1$ and $L=\max\{4,N\}$. Every listed
state and transition is installed and counted. The zero entry correctly
tests the four possible right alphas and returns the whole required row
on every actual source within four calls, by Proposition 1.4.

Agreement with every expected constructor at the actual nodes of a
fixed finite tree is equivalent to equality with that tree. Structural
induction proves this: a matching leaf ends both subtrees, and a matching
branch requires its two child inductions. A missing or extra branch
fails at a tested constructor, including at a leaf boundary. Therefore
the one entry reaches $H_0$ exactly when the current tree is $t^*$;
on every other tree a first mismatch enters the divergent self-loop.
Injectivity of $\rho$ makes that unique source exactly $u^*$.

Consequently $G(u^*)=\{0,1\}$ and $G(u)=\{0\}$ for every other
actual $u$. The acquired-term code equal to one exactly on $X^*$ and
zero elsewhere is lawful and compatible. Both bits are attained, for
example at $u^*$ and any positive source. But any both-attained
compatible code must assign one at $u^*$: there is no other source at
which one is good. Hence its good label zero is not extendible.

All Read words have maximum relative hole suffix depth six, so this
table's $b$ is six. Each $B_i$ is fully exposed at that depth, including
its beta leaves. The cell of $u^*$ is therefore closed and singleton,
in agreement with (FCS.19) and (FCS.24). This example also shows why
divergence at unchosen entries must remain allowed. $\square$

## 8. Exhaustive finite certificates and their verifier contracts

**Definition 8.1 (positive certificate).** The public native model,
explicit $T$, its original labeled entries and $L$ are the fixed verifier
input. A positive certificate contains $b$, the entire ordered retained
profile inventory with shared class terms, the image and whole-term
syntax-test data, closed/live flags, every installed-state reply vector,
every complete target row, both bounded entry paths and good sets, and
a passing ordered pair from (B). It also contains two different ground
class tuples realizing that pair, their selected good bits, and the
finite defaults and tuple-exception specification (FCS.23).

The verifier first checks the finite table contract, including its
state partition, all four successors and distinct original entries.
It recomputes $b$ from every installed Read. It then regenerates all
bounded candidate patterns, applies (FCS.16), and requires exact equality
with the retained inventory. Merely checking that the listed profiles
are feasible is insufficient: omissions must be detected. It recomputes
the whole-term negatives for every pair of different classes, all
installed replies, closed/live flags, complete canonical target rows,
both bounded paths and (A),(B).

For the two ground tuples it checks finite syntax, every class
disequality, whole image membership, the selected profiles, distinctness
and their corresponding good labels. The inverse parser verifies their
actual finite origins. It can regenerate the specified height-tag
witnesses directly; alternatively any supplied tuples passing all these
ground tests suffice. Finally it regenerates the finite default and
two-exception encoder template. It verifies this canonical specification,
not arbitrary substituted program text. Requiring a fixed order and
the first passing pair gives a canonical choice if desired.

**Definition 8.2 (negative certificates).** Negative verification uses
the same exhaustive regenerated inventory, whole outputs, replies and
entry paths. One negative type identifies an actual retained cell with
$G_\eta=\varnothing$ and supplies its ground image filling. The other
has (A) true but no passing ordered pair in (B), as checked over the
entire finite inventory using its exact multiplicities. Both require
recomputation rather than trusting flags or a list of sampled sources.

**Theorem 8.3 (sound, complete and terminating certificate specification).**
These finite certificate contracts decide exactly nonemptiness of
$\mathcal C_L(T)$ and certify a lawful BOTH-bit-attained code on a
positive answer, with the original table and entries unchanged.

Proof. The bounded recursion enumerates a finite candidate family.
Structural tests and finite free-term equality terminate. Proposition
4.3 proves that the regenerated retained inventory has no spurious
actual cell and omits none. Lemma 4.2 and Theorem 4.4 justify every
multiplicity flag and the constructed actual witnesses. Proposition
2.2 and Lemma 5.2 justify all full target rows, response vectors and
bounded acceptance paths. In particular initial Halts, last-call Halts,
wrong entire outputs, cycles, absent replies and unused-entry divergence
have exactly their prescribed treatment.

With positive checks, Theorem 6.1 makes the regenerated encoder lawful,
both-attained and correct on the entire actual domain. Conversely a
nonempty class implies (A),(B), and the finite witness and default
construction gives a certificate of that form. If a negative cell has
no good label, its actual ground realization admits neither entry
within the bound, excluding every compatible code. If (A) holds but
(B) fails, any purported both-attained code would give two different
actual points contradicting that exhaustive failure, by Theorem 6.1's
necessity. Every empty class therefore has one of the stated negative
certificates. The finite scans, ground checks and bounded state paths
all terminate.

These are mathematical verifier contracts, not executed checks or a
claim that any arbitrary code program can be semantically verified.
Certificate completeness does not give a small certificate or an
efficiency bound. No determining assignment for an original code, source
oracle or promised compatible computation is used. $\square$

## 9. Sourcewise termination without an imposed call bound

**Theorem 9.1 (stationary no-revisit reduction).** For the same explicit
finite table, lawful both-attained compatibility requiring correct
termination on each source, with no supplied call cap, is exactly
$\mathcal C_{|Q|}(T)$. Thus all preceding criteria and constructions
apply with $L=|Q|$.

Proof. Fix one stationary actual source and an entry. At a given Read
the fixed address has a fixed reply. Reentering that state repeats
its identical deterministic future forever, so a terminating run
cannot revisit a Read. It therefore uses at most $|Q|$ calls, and
may instead begin in a Halt with zero calls. This is NBP Proposition
12.5 and PCA Lemma 2.3's sourcewise no-revisit argument on precisely
the present table contract. Correct termination of each selected
entry implies the stated bound on that source; the reverse implication
is immediate.

An unchosen entry may loop or fail. Its label is simply absent from
the good set. No promise that both entries terminate on each source
is added. Different sources may use different successors and their
union of paths may contain cycles; the no-revisit argument fixes one
source. All installed unused Reads and their words still belong to
the input. This reduction extracts no finite state space, address
menu or table contract from arbitrary reader-program text. $\square$

## 10. Arbitrary acquired-program verification remains undecidable

**Definition 10.1 (one fixed eight-state table).** Install exactly
$\mathsf B_1,\mathsf B_2,\mathsf B_3,H_0,H_1,H_2,H_3,H_4$, with the
three Reads and five whole-row Halts below, and fix
$e_0=\mathsf B_1$, $e_1=\mathsf B_3$, $L=2$. The upright Read names
are distinct from the ground image trees $B_n$ of (FCS.8).

| Read | Literal | On alpha | On beta | On branch | On absent |
| --- | --- | --- | --- | --- | --- |
| $\mathsf B_1$ | $LLR$ | $H_1$ | $H_0$ | $\mathsf B_2$ | $H_0$ |
| $\mathsf B_2$ | $LRR$ | $H_2$ | $H_0$ | $H_0$ | $H_0$ |
| $\mathsf B_3$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

Each $H_j$ stores literally the entire $R_j$ of (FCS.9)–(FCS.10),
including its hole order, recomputed names, every different-class
disequality and its concrete beta guards. No Halt issues a target
index for a source-dependent decoder. These are PCA Supplier application
4.3 and NBP Theorem 15.5's entries with $S=\{1,2\}$ and distinguished
test $3$, specified here with every successor.

**Theorem 10.2 (verification separation under totality, attainment and
finite-preparability promises).** There is no effective procedure that,
on every acquired-term code program promised total, BOTH-bit-attained
and finitely preparable on $\mathcal U_*$, decides whether that program
belongs to $\mathcal C_2(T)$ for the one fixed table in Definition
10.1. Here finite preparability means generation of its original bit
and literal entry code under a separately supplied paid common-start
native-preparation permission. It does not promise that this reader
correctly recovers the whole row for an incompatible code.

Proof. First define the lawful baseline

$$
\sigma^{\mathrm{base}}(u)=
\begin{cases}
1,&u\in\Pi_3\cup\Pi_4,\\
0,&\text{otherwise}.
\end{cases}
\tag{FCS.27}
$$

Roots of acquired finite terms determine this bit. The table verifies
it on every actual case: from $e_0$, $\Pi_1$ reaches $H_1$ and
$\Pi_2$ reaches $H_2$; every zero profile reaches $H_0$, including
beta at $b_1$ or $b_2$. From $e_1$, $\Pi_3$ reads alpha at $b_3$
and reaches $H_3$, while $\Pi_4$ reads branch there and reaches
$H_4$. These cases exhaust the prescribed entry choices. All outputs
are the complete required rows and all runs use at most two calls.
Both bits are attained.

Let $e$ be any finite deterministic machine description with specified
initial configuration. Use PCA Definition 15.1's stage convention:
the first halt stage $\tau$, if it exists, is at least one and stage
one includes the initial-Halt check. For a finite tree $B$, let $h(B)$
be its maximum leaf depth. Define a program equal to the baseline
except on $\Pi_1$, where it computes

$$
\sigma_e(u)=
\mathbf1_{\{e\text{ halts within }h(x_c)\text{ stages}\}}
\qquad(u\in\Pi_1).
\tag{FCS.28}
$$

The program is described effectively from $e$. Finite root inspection
determines the case, structural recursion computes the acquired term's
finite height, and the simulation is bounded by that height. Thus it
terminates on every acquired finite input, with a fallback on malformed
representations. There is no decision of eventual halting inside this
code. On $\Pi_2$ its bit is always zero and on $\Pi_3$ always one,
so every program in this family attains both values.

If $e$ never halts, $\sigma_e$ is exactly the compatible baseline.
If it halts first at $\tau$, take the explicit class values

$$
x_a=\beta,\quad x_{b_1}=\alpha,\quad
x_c=B_\tau,\quad x_{b_2}=B_{\tau+1},\quad
x_{b_3}=B_{\tau+2},\quad x_{b_4}=B_{\tau+3}.
\tag{FCS.29}
$$

Since $\tau\ge1$, the four latter values are distinct finite branch
images, different from both leaves. Both partner occurrences repeat
their one class value. This is an injective $\Pi_1$ image filling,
so (FCS.7) gives an actual finite origin in the original full fiber.
It has $h(x_c)=\tau$ and hence bit one under (FCS.28). From $e_1$
the actual reply at $b_3$ is branch, so the table returns the entire
$R_4$ after one call. The required row is the different $R_1$.
Therefore

$$
\sigma_e\in\mathcal C_2(T)
\quad\Longleftrightarrow\quad e\text{ never halts}.
\tag{FCS.30}
$$

Every one of these original codes is also finitely preparable, by
cases. In the nonhalting case the six class roots determine the
baseline. In the halting case (FCS.28) is the predicate
$h(x_c)\ge\tau$ on $\Pi_1$. For a finite tree this holds exactly
when some word of length $\tau$ has nonabsent reply: a longest
root-to-leaf path has a node at that level if and only if its length
is at least $\tau$. Thus the finite menu

$$
\{p_d:d\in D\}\ \cup\
\{p_cw:|w|=\tau\}
\tag{FCS.31}
$$

determines the original code in the halting case, with actual absent,
leaf and branch replies interpreted literally. One occurrence of $c$
suffices because both occurrences contain the same term.

For completeness, the generation part of PCA Theorem 3.2's finite
prefix/latch construction applies independently of subsequent reader
correctness. Order a determining menu as $w_1,\ldots,w_m$. For every
attained reply prefix of length $j<m$, install a running state that
queries the fixed word $w_{j+1}$. An attained extension enters its next
prefix state, or at length $m$ the latch for the determined literal
entry $e_0$ or $e_1$. Every unattained extension is sent to one fixed
existing latch. The common start is the empty-prefix state; an empty
menu instead starts at its constant latch. This specifies every
four-reply successor. Induction gives the exact original code on every
source after finitely many calls. The prefix identities are counted
states, not a free history register or computed-address facility. The
last transition replaces control by the complete code latch, and the
separately paid handoff enters exactly that original $e_z$ with all
preparation material inaccessible.

This proves finite preparability for both cases, including when the
reader fails for the generated bit. It makes no uniform choice between
halting and nonhalting, and extracts no $\tau$, determining menu,
halting-time bound or preparer from the input program. All native
permissions, paid calls, latch storage, isolation and entry remain
separate supplied conditions.

A purported compatibility decider on the promised programs can now
be applied to the effectively described $\sigma_e$. Every such input
satisfies all three promises. By (FCS.30) complementing its answer
decides eventual halting of arbitrary finite descriptions, contradicting
the halting endpoint used in PCA Theorem 15.2. This is a direct native
reduction with actual large-height $\Pi_1$ witnesses, rather than an
appeal to a generic program-verification slogan. $\square$

## 11. Relationship to common normalization and original-code acquisition

**Corollary 11.1 (removing the nonempty-class promise for an explicit
table).** For a supplied table with at most nine installed states and
$L=2$, Theorem 6.1 decides and certifies the nonemptiness premise needed
by TCR's common-normalization theorem. On a positive answer, TCR Theorems
4.2, 6.3 and 7.1 apply under their original operational contract: one
table-determined exclusive positive-fiber pair supplies one shared
nine-state, at-most-four-call representative-root reader with a fixed
faithful entry map for every code served by the input table.

Proof. The source, five full outputs, acquired-data services, all
installed-state conventions and fixed labeled entries in §§1–3 match
TCR Definitions 2.1–3.2 exactly at these restricted parameters. TCR
Proposition 3.4 proves that every code in its original two-call class
already attains both bits. Hence that class is precisely
$\mathcal C_2(T)$, not a class obtained by silently changing an attained
alphabet. A positive certificate from Theorem 8.3 supplies its required
nonemptiness. The stated normalization is then the direct cited
consumer TCR Theorem 7.1 with its own bounds and quantifiers; no root
normalizer is reproved or generalized here. $\square$

**Convention 11.2 (selection, verification and generation are separate).**
Theorem 6.1 chooses some new lawful code for an explicit table. It
neither verifies a separately supplied program nor recovers its original
pointwise values. Theorem 10.2 proves the strict verification obstruction
even under the stated strong promises. Finite correct-entry sets need
not determine which good bit an independently prescribed program chooses.

PCA Theorem 8.2 concerns a compatible original code whose varying
$Z_{b_3}$ predicate asks whether an entire acquired branch image contains
alpha. No finite stationary fixed-address common-start preparer generates
that original code on the whole domain, even with sourcewise termination
alone. PCA Theorem 15.2 concerns total, finitely preparable original code
programs sharing the fixed eight-state reader, for which no uniform
extractor returns a determining depth, menu or original-entry preparer.
Both conclusions retain their full original-code scope. This volume
does not generate the former code or extract the latter certificates.
The verifier separation in §10 uses its own explicit program family;
its finite-preparability promise is code generation, not whole-row
success for an incompatible program.

The new code (FCS.23) uses acquired whole-tuple exceptions and is not
assigned any bounded native preparation implementation by this theorem.
A preparer denied the acquired values is not granted them. Supplying
a determining certificate for an original code, bounding a preparer's
states, calls or literal submissions, and optimizing correlated
preparation/reader costs remain distinct questions with the permissions
of PCA §§10–14. No pending bounded-preparer result is a premise here.

## 12. Provenance and exact limits

**Convention 12.1 (inherited content and additional deductions).** The
mathematical ownership and parameter correspondence are the following.

| Canonical supplier | Exact use here |
| --- | --- |
| NBP Definitions 1.1–1.2 and 9.1; Propositions 9.3 and 15.2; Theorem 10.4 | Original ordered finite trees, literal four-reply reading, full actual inverse fiber, injective image valuations, repeated partners, all eleven actual root cases and five complete canonical predecessor rows in §§1–2. |
| NBP Assumption 9.2 and Definitions 11.1 and 15.1; PCA Assumptions 1.2 and 16.1; TCR §3 | Acquired-term code, actual export, complete isolation, faithful original labeled entries, one stationary register and every installed state and actual invocation charged in §3. |
| PCA Definition 11.1, Theorem 11.2 and Proposition 11.3 | Our six free terms are its $T_d$, our relative depth is its inclusive $b$, our image predicate and entire negative list are its (PCA.26)–(PCA.27). Exact actual attainment is inherited; no determining certificate is needed for that statement. |
| TCR Definition 5.1, Lemma 5.2 and Proposition 5.3 | Installed-menu depth, literal patterns, simultaneous finite branch-image filling and exact source coverage. The height-tag calculation in §4 is the same needed finite-term specialization, with closed pieces and whole-class negatives retained. |
| TCR Definition 6.1 and Lemma 6.2 | Truthful installed-state response vectors and complete-output bounded entry tests. Section 5 substitutes the arbitrary finite input $L$ for the bound two; it adds no general automata theorem. |
| NBP Proposition 12.5; PCA Lemma 2.3 | Fixed-source stationary no-revisit and the $|Q|$ reduction in §9, with cycles across different-source paths still allowed. |
| PCA Supplier application 4.3; NBP Theorem 15.5 | The original eight-state reader and faithful entries, displayed completely in §10. |
| PCA Theorem 3.2, generation construction; Definition 15.1 and Theorem 15.2 | Finite-menu prefix/latch generation, bounded simulation on acquired finite data and the halting endpoint. Section 10 supplies the separate actual-source reduction for membership verification. |
| TCR Theorems 4.2, 6.3 and 7.1; Proposition 3.4 | A direct common-normalization consumer under its own at-most-nine-state, two-call and matching attained-alphabet hypotheses, as in §11. |

The additional elementary conclusions are the exact singleton versus
countably infinite multiplicities, the two-distinct-actual-point
surjective-selector criterion, the total lawful default-and-exceptions
construction without a compatible-code promise, and the pointwise
extendible-label formula with its actual singleton example. The finite
certificate contracts consume these results. The fixed-table promised
program-verification reduction adds the separation from choosing some
compatible code. Finite selection, term comparison and stationary
determinism are elementary methods; the inherited native profile and
filling theorems are not presented as new classifications.

**Convention 12.2 (evidence and unresolved realization boundaries).**
The proofs establish ordinary mathematical statements under the named
acquisition and service premises. They are not current Lean/kernel
evidence or executed synthesis, numerical, experimental or test results.
The provenance assessment is bounded to the named supplied mathematical
sources; it makes no literature-wide priority or exhaustive external
research claim.

The finite input must really be the explicit stationary fixed-literal,
state-only table with all its configurations and transitions exposed.
No theorem extracts that contract from arbitrary program text with
computed addresses, hidden workspace or other source inputs. Only
selected entries need succeed; extra universal entry-totality would
change the problem. Changed cuts, domain restrictions, extra ports,
updates, randomization or restrictions on the producer require new
correspondences.

Acquisition and representation of the complete current row and finite
terms, producer constants and workspace, local work, authentication,
installation, fixed table and address storage, whole-output storage,
actual export, complete access isolation, lawful new entry and
continuing native service retain their separate permissions and prices.
Zero fresh queries in a local acquired-term computation is not free
acquisition. Finite decidability gives no efficiency, small-program,
physical-memory, time, energy or empirical machine-learning conclusion.
No physical implementation, arbitrary original-code recovery,
budgeted-preparation optimum or completion of the broader native
relational-fiber programme follows.

[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[TCR]: FIB_TABLE_DRIVEN_COMMON_ROOT_NORMALIZATION.md

## 追加锚（本行以下为增补区）
