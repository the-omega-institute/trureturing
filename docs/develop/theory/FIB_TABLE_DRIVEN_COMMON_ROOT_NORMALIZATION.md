# Table-driven common root normalization for prescribed binary codes

> This is an append-only `generic-v1` reference volume. Its locators depend
> on its own Markdown bytes. Corrections and extensions belong in numbered
> sections after the final append anchor; existing sections remain intact.

## 1. Scope, status and canonical suppliers

Fix a stationary arbitrary-literal Moore table with at most nine installed
states, its two labeled faithful entries, and the class of all lawful
acquired-term binary codes that it serves on the entire repeated-partner
one-image fiber within two calls. Assuming this class is nonempty, this
volume proves that one positive fiber forces the same unique correct entry
for every member of the class. A terminating finite procedure on the table
alone finds that fiber and entry, produces an exhaustive finite certificate,
and specifies one nine-state, four-call representative-root reader serving
every compatible code with its original pointwise value.

The canonical abbreviations are NBP for [*Native cut-birth provenance and
literal past-row recovery*][NBP], NRE for [*Prescribed binary codes: a
nine-state escape from root-only two-call reading*][NRE], NRN for
*Prescribed binary codes: nine-state root normalization*, and PCA for
[*Native prescribed-code acquisition on the original one-image fiber*][PCA].
Each use below identifies its numbered owner. In particular, NRN Theorem
6.1 supplies the per-code constant-positive-fiber theorem; its proof is not
a new result of this volume.

This is `repo-derived` ordinary paper mathematics, authored by the sole
Codex CLI author. The named suppliers retain ownership of inherited
results. This reference input carries no Lean kernel certification,
executed mathematical verification, literature-wide originality claim or
empirical interpretation. Acquisition and service hypotheses remain
conditions of the mathematical statements.

## 2. Native objects, the full fiber and five complete rows

**Definition 2.1 (finite native source and complete row).** Reuse NBP
Definitions 1.1–1.2 and Proposition 9.3, and NRN Definitions 2.1–2.2.
The sources are all finite nonempty ordered terms

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
\tag{TCR.1}
$$

In the native Boolean notation, true is alpha and false is beta, while
false and true address letters are $L$ and $R$. Every finite word in $L,R$,
including $\varepsilon$, is a legal literal query. The actual reply
$r_t(v)$ is alpha or beta at that leaf, $\mathsf{branch}$ at a pair, and
$\mathsf{absent}$ outside the finite tree. Every strict continuation of a
leaf is absent. At an existing occurrence $p$,

$$
r_t(pw)=r_{t|_p}(w)
\qquad\text{for every finite suffix }w.
\tag{TCR.2}
$$

Equality retains ordered brackets and both leaf labels. Different
occurrences of equal subtrees remain different occurrences.

For a finite prefix-free cut $P$, its complete row $R_P(t)$ consists of
the whole exterior after replacing the subtree at each reached cut
occurrence by its occurrence hole, and the complete equality partition
of the replaced subtrees. Different classes assert disequality. Every
unreached cut has a concrete blocking leaf at a strict prefix in the
exterior. In lexicographic order of the reached holes, a class is named
by the zero-based position of its first member. Names are recomputed
after restriction and need not be consecutive.

The inherited exact image grammar and inverse are

$$
\begin{aligned}
\mathcal I=\rho[\mathcal T]&::=\beta\mid E\mid
                                  \langle\mathcal I,\mathcal I\rangle,\\
\delta(\beta)&=\alpha,\qquad \delta(E)=\beta,\\
\delta\langle y,z\rangle&=\langle\delta y,\delta z\rangle
                                      \quad(y,z\in\mathcal I).
\end{aligned}
\tag{TCR.3}
$$

These disjoint recursive cases give inverse maps on the stated domains.
Thus $\rho$ is injective, alpha is not an image, and beta is the only
image leaf. Every branch subtree of an image is an image, by the same
grammar, as used in NBP Proposition 10.2 and PCA Theorem 11.2. Write
$\mathcal B=\mathcal I\setminus\{\beta\}$ for the branch images.
NBP Theorem 3.3 and Proposition 15.2 supply infinitely many distinct
members, $\rho^m\alpha$ for $m\ge2$.

**Definition 2.2 (unchanged entire actual domain).** Fix NBP Definition
9.1's cut $P=\{L,R\}^3$ and complete current row $R_*=(C_*,\pi_*)$.
The exterior is perfect through depth three and its partition has exactly
the following six classes, with every different-class disequality:

| Class alias | Representative $p_d$ | All occurrence holes |
| --- | --- | --- |
| $a$ | $LLL$ | $LLL,LRL$ |
| $c$ | $RLL$ | $RLL,RRL$ |
| $b_1$ | $LLR$ | $LLR$ |
| $b_2$ | $LRR$ | $LRR$ |
| $b_3$ | $RLR$ | $RLR$ |
| $b_4$ | $RRR$ | $RRR$ |

Put $D=\{a,c,b_1,b_2,b_3,b_4\}$ and $J=\{1,2,3,4\}$. The aliases
refer to the canonical classes, rather than additional acquired values.
For a class valuation $x:D\to\mathcal T$, define

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{TCR.4}
$$

The domain and whole target are exactly

$$
\mathcal U_*:=\{u\in\mathcal T:R_P(\rho u)=R_*\},
\qquad t_u=\rho u,\qquad F(u)=R_P(u).
\tag{TCR.5}
$$

All finite origins satisfying this equation are included, without a
bound on size, depth, rank or internal branch structure. NBP Proposition
9.3 and the legal-row fiber identify this domain with precisely the
injective valuations $x$ for which $\mathscr S(x)\in\mathcal I$:
the actual finite origin is $\delta(\mathscr S(x))$. Both occurrences
of each partner receive the same value. This inverse constructs a
mathematical witness and supplies no physical inverse operation.

**Definition 2.3 (full fixed Halt outputs).** Reuse NBP Proposition
9.3, NRE Definition 2.2 and NRN Definition 2.3. Write
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$. The five rows
$R_h=(C_h,\pi_h)$ have these complete exteriors:

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
\tag{TCR.6}
$$

Their complete partitions are

$$
\begin{aligned}
\pi_0&=\{\{LLL,LRL\},\{LLR\},\{LRR\},
                      \{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_1&=\{\{LRL\},\{LRR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_2&=\{\{LLL\},\{LLR\},\{RLL,RRL\},\{RLR\},\{RRR\}\},\\
\pi_3&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RRL\},\{RRR\}\},\\
\pi_4&=\{\{LLL,LRL\},\{LLR\},\{LRR\},\{RLL\},\{RLR\}\}.
\end{aligned}
\tag{TCR.7}
$$

Different blocks assert disequality in each partition. The canonical names
and all absence guards are part of the rows:

| Row | Ordered reached holes | Canonical name vector | Absent cuts and their concrete guard |
| --- | --- | --- | --- |
| $R_0=R_*$ | $LLL,LLR,LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,0,3,4,5,4,7)$ | None |
| $R_1$ | $LRL,LRR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LLL,LLR$; beta at $LL$ |
| $R_2$ | $LLL,LLR,RLL,RLR,RRL,RRR$ | $(0,1,2,3,2,5)$ | $LRL,LRR$; beta at $LR$ |
| $R_3$ | $LLL,LLR,LRL,LRR,RRL,RRR$ | $(0,1,0,3,4,5)$ | $RLL,RLR$; beta at $RL$ |
| $R_4$ | $LLL,LLR,LRL,LRR,RLL,RLR$ | $(0,1,0,3,4,5)$ | $RRL,RRR$; beta at $RR$ |

In $R_1,R_2$ the other occurrence of $a$ survives as a hole; in
$R_3,R_4$ the other occurrence of $c$ survives. Only the selected pair
at $q_j$ is replaced by a concrete beta. Distinct reached supports make
these five rows different. Each Halt used below stores its entire row,
including all this data.

**Supplier 2.4 (all actual profiles and their targets).** Apply NBP
Propositions 9.3 and 15.2, equivalently NRN Supplier 2.4, on (TCR.5).
Let $g(1)=g(2)=a$ and $g(3)=g(4)=c$. The following eleven nonempty
sets are disjoint and exhaust the entire domain:

$$
\begin{aligned}
\Pi_j:&\quad x_{b_j}=\alpha,\quad x_{g(j)}=\beta,
       \quad\text{the other four values are branch images},\quad j\in J;\\
Z_d:&\quad x_d=\beta,
       \quad\text{the other five values are branch images},\quad d\in D;\\
Z_*:&\quad\text{all six values are branch images}.
\end{aligned}
\tag{TCR.8}
$$

Every indicated finite filling is allowed subject to the original
whole-class disequalities, and has its actual inverse origin. The whole
target is $R_j$ on $\Pi_j$ and $R_0$ on every $Z_d,Z_*$.
Thus zero includes beta at either partner, at any of the four right
classes, and nowhere. No branch-family restriction is introduced.
Every word shorter than three reads the common exterior branch. Every
word of length at least three is uniquely $pw$ with $p\in P$, and (TCR.2) reads the
suffix in the actual value of class $[p]$; this includes arbitrary
depth, either repeated occurrence and every absent continuation.

Each $\Pi_j$ is infinite. Fix three of its four free branch values
distinctly and vary the fourth through the infinite branch-image set
avoiding those three. Supplier 2.4 and injectivity of $\rho$ give
different actual finite origins for all these choices.

## 3. Supplied services, fixed table and compatible code class

**Assumption 3.1 (acquisition, export, entry and stationary service).**
Keep NBP Assumptions 9.2 and 10.6 and Definition 15.1, NRE Assumption
3.1, and NRN Assumption 3.1. Exactly one genuine authenticated update
binds the actual origin $u$ to the same current register $t_u=\rho u$.
The cut, root and version are fixed; there is no reset, rotation, source
replacement, arbitrary edit or subsequent update. Authentication and
version binding convey no additional origin distinction within the fiber.
The complete current row is lawfully acquired on this stationary version.

Before the complete access cut the producer genuinely possesses
same-source, same-version finite data $A(u)$: either the lossless current
tree or $R_*$ and one acquired finite subtree value for each of the six
classes. Equality comparisons concern these acquired finite terms.
A lawful code is a specified terminating finite computation on these
data with complete value in $\{0,1\}$. Internal structure dependence
is permitted. The producer computes and actually exports that original
complete bit with the row before access to the acquired material is lost.

A supplied lawful common entry exposes exactly this complete bit,
$P,R_*$ and common source-independent controls, with these inputs
recoverable at entry. No further source-dependent origin identifier,
predecessor, alpha marker, acquired value, trace, cache, old output,
archive, pointer, allocation, control field, acquisition order or count,
length, meter, timing or update packet is accessible. A field determined
by the declared payload adds no distinction; any other field changes
the contract. Inaccessible material need not be physically erased.

The current register remains stationary throughout fresh reading.
Its only source port is the four-reply literal port of Definition 2.1.
There is no unknown-subtree equality, image, provenance, generation,
inverse or extra subtree port. Every invocation counts, including
repeats, absences, leaf continuations and addresses previously used in
acquisition. Acquisition, finite local acquired-term computation,
authentication, version binding, installation, actual export, complete
isolation, faithful lawful entry and authentic continuing native service
are supplied and separately priced. An absorbing producer stop grants
no resume operation; later reader entry is a separately supplied
invocation. A representation of a row or code supplies none of these
services.

**Definition 3.2 (table fixed before any pair is chosen).** Fix one
finite installed table $T$ on $\mathcal K=Q\sqcup H$, with
$|\mathcal K|\le9$, and fixed functions

$$
\begin{aligned}
\operatorname{addr}&:Q\to\{L,R\}^{*},\\
\operatorname{next}&:Q\times\mathcal A\to\mathcal K,
 &\mathcal A&=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\},\\
\operatorname{out}&:H\to\{\text{complete rows at }P\}.
\end{aligned}
\tag{TCR.9}
$$

Also fix its labeled distinct entries $e_0,e_1\in\mathcal K$.
Entry for a bit $z$ is $e_z$, with the fixed inverse labeling recovering
that bit. A Read makes exactly one paid invocation at its fixed literal
and replaces the state by its fixed successor for the reply. A Halt
returns its fixed entire row without a call. All four successors are
installed at every Read. Every installed state counts, including
unused Reads, unused Halts and distinct Halts with identical outputs.

After entry the current member of $\mathcal K$ is the whole mutable
accessible source-dependent memory. There is no retained bit copy,
reply or address register, computed address, independent program counter,
phase, clock, counter, history, archive, table selector or output decoder.
There is no free control transition. Sharing, repeated words, early
Halts and cycles in unions of different-source paths are allowed; a
required run must actually terminate within its call budget. These are
the exact state conventions of NBP Definition 11.1, NRE Definition 3.2
and NRN Definition 3.2.

For this fixed table and these fixed labels define $\mathcal C(T)$ to
be the full class of lawful acquired-term codes $\sigma$ of Assumption
3.1 such that, for every $u\in\mathcal U_*$, execution from
$e_{\sigma(u)}$ returns the entire $F(u)$ within two actual calls.
The computation of $\sigma$ and its pointwise values are held fixed
when asking whether it belongs to this class. No recoding of it into
an initial-state code is permitted. Assume throughout the main results
that $\mathcal C(T)\ne\varnothing$; this is a promise, not a decision
task here. All of $T,e_0,e_1,\mathcal C(T)$ are fixed before choosing
any positive index or bit.

Define the allowed correct-entry set on every actual origin by

$$
G_T(u):=\{z\in\{0,1\}:T\text{ from }e_z\text{ on stationary }t_u
       \text{ Halts with the whole }F(u)\text{ within two calls}\}.
\tag{TCR.10}
$$

This definition imposes no promise on the other entry's run. It can
Halt incorrectly, cycle, or still be running after two calls. Every
$\sigma\in\mathcal C(T)$ selects $\sigma(u)\in G_T(u)$ at every
actual origin, so nonemptiness of the class implies nonemptiness of
every $G_T(u)$.

**Supplier 3.3 (the canonical per-code obstruction).** NRN Theorem 6.1
states that a lawful prescribed binary code admitting an arbitrary-literal
reader with at most nine installed states and at most two calls on the
entire original domain is constant on some entire $\Pi_j$. Apply it to
any $\sigma\in\mathcal C(T)$. Its source and whole outputs are
Definitions 2.1–2.3, its full domain is (TCR.5), its acquired/exported
services are Assumption 3.1, and its fixed-code state-only table is
Definition 3.2. Thus

$$
\forall\sigma\in\mathcal C(T)\quad
\exists j\in J\ \exists z\in\{0,1\}\quad
\forall u\in\Pi_j,\quad\sigma(u)=z.
\tag{TCR.11}
$$

Only this numbered inherited theorem supplies (TCR.11). Its quantifiers
alone do not choose a common pair across different codes.

**Proposition 3.4 (one attained bit cannot meet the two-call premise).**
No member of $\mathcal C(T)$ has a singleton attained alphabet. This
does not assume that both entries are used in advance.

Proof. Reuse NBP Proposition 15.2's movable actual six-source family.
Choose six distinct branch images $B_d$. On indices
$0_a,0_c,1,2,3,4$, set $a$ to beta on $\{0_a,1,2\}$ and to
$B_a$ otherwise; set $c$ to beta on $\{0_c,3,4\}$ and to $B_c$
otherwise; set $b_j$ to alpha only at $j$ and to $B_{b_j}$ otherwise.
Every tuple is injective and satisfies Supplier 2.4, so it has an
actual finite inverse origin. Their five required whole outputs are
$R_0,R_0,R_1,R_2,R_3,R_4$.

Every finite word has at most two replies on these fixed actual
sources: exterior words are constant, a partner cone reads one of its
two fixed trees, and a right cone reads alpha at its index or its one
fixed branch image elsewhere. Equation (TCR.2) includes all deep and
absent continuations. If only one bit is attained, all six sources
start at its one common entry. A deterministic execution tree with
at most two calls and at most two replies per call has at most four
terminal leaves. This follows recursively: an initial Halt has one
leaf, one call has at most two, and two calls at most twice two;
early stopping cannot increase the count. Each leaf has one fixed
whole output. It cannot return five different required rows.
An unused labeled entry changes none of these actual paths. $\square$

## 4. Lawful finite edits and a common forced pair

**Lemma 4.1 (closure under finite allowed edits).** Fix
$\sigma_0\in\mathcal C(T)$. Let $V\subseteq\mathcal U_*$ be finite
and assign $b_v\in G_T(v)$ to each $v\in V$. The function equal to
$b_v$ at $v$ and equal to $\sigma_0$ elsewhere is a member of
$\mathcal C(T)$ under the same acquisition and entry contracts.

Proof. Each $v$ has a finite current tree $\rho v$ and its finite
six-class tuple. Store these finitely many ground terms in the
pre-cut computation. If its input is the acquired current tree,
compare it with the stored current trees. If its input is the row
and acquired values, compare all six values with each stored tuple
in fixed class order. Equality of finite ordered terms is decided by
recursion: leaf constructors must agree; for pairs compare both
children; unequal constructors fail. It terminates because the terms
are finite. Local extraction at the fixed representatives from an
already acquired lossless tree is also finite local computation.
Neither operation queries an unacquired subtree or the native source.

The complete current tuple determines $\mathscr S(x)$, and injectivity
of $\rho$ makes it determine its unique origin. Thus these comparisons
identify exactly the specified finite exceptions, including both
occurrences of each partner. On a match return the selected bit;
otherwise run the lawful terminating computation for $\sigma_0$.
This is one terminating finite acquired-term computation on the full
domain. Its additional producer constants, comparisons and workspace
have their separate costs; they are not reader states or free queries.
Assumption 3.1 supplies actual export of its resulting complete bit
before the cut, complete isolation and lawful entry at the same $e_z$.

At an exception the selected bit belongs to $G_T(v)$, so the original
fixed table is correct within two calls there. Elsewhere its input
bit and hence its actual run remain those for $\sigma_0$. The table,
labels and domain have not changed. This proves compatibility of the
edited lawful code on every actual origin. $\square$

**Theorem 4.2 (common exclusive-entry positive fiber).** Under
Definitions 2.1–3.2 and the promise $\mathcal C(T)\ne\varnothing$,
there exist $j\in J$ and $z\in\{0,1\}$ such that

$$
\forall u\in\Pi_j,\quad G_T(u)=\{z\}.
\tag{TCR.12}
$$

Consequently this same pair satisfies

$$
\forall\sigma\in\mathcal C(T)\ \forall u\in\Pi_j,
\quad\sigma(u)=z.
\tag{TCR.13}
$$

Proof. Choose one $\sigma_0\in\mathcal C(T)$ for existence reasoning.
Every actual $G_T(u)$ is nonempty. Suppose that no pair satisfies
(TCR.12). For each fixed $j$, some point of $\Pi_j$ allows 0 and
some point allows 1. Indeed, if 0 were allowed nowhere, every
nonempty set there would be $\{1\}$, giving the forbidden pair
$(j,1)$; the argument excluding absence of 1 is identical.

Choose points allowing the respective bits. They can be chosen
distinct. If the initial two choices coincide, that point allows both
bits. Take any different point of the infinite $\Pi_j$ and choose
one of its allowed bits. Use that bit at the new point and the
opposite bit at the original point. This gives distinct actual
$v_{j,0},v_{j,1}\in\Pi_j$ with $b\in G_T(v_{j,b})$ for
$b=0,1$. The four positive fibers are disjoint, so all eight points
are different across the four fibers as well.

Apply Lemma 4.1 to these eight points, assigning bit $b$ at
$v_{j,b}$. The resulting lawful code is still served by the same
fixed $T,e_0,e_1$ on the whole domain, and attains both bits on
every entire positive fiber. This contradicts the inherited per-code
obstruction (TCR.11). Thus (TCR.12) holds. Every compatible code
selects an element of $G_T(u)$, proving (TCR.13).

Only finitely many ground comparisons were added to an existing
lawful computation. No arbitrary extensional coloring was declared
lawful, and no value of that chosen computation is needed as input
to the table-only construction below. $\square$

## 5. Exact finite profiles of the installed address menu

**Definition 5.1 (bounded patterns, image test and whole-class negatives).**
For each installed Read word of length at least three, write it as
$pw$, $p\in P$, and retain its queried class and suffix. Set

$$
b=\max\bigl(\{0\}\cup
 \{|w|:\operatorname{addr}(k)=pw,\ p\in P,\ k\in Q\}\bigr).
\tag{TCR.14}
$$

The maximum includes every installed Read, even unused states,
duplicate words and states queried only from a wrong entry. Words
shorter than three are exterior-constant. No bound on actual source
size follows from this finite menu bound.

At each class enumerate all finite prefix patterns through inclusive
relative depth $b$. At a node before depth $b$, choose alpha, beta,
or a branch with two recursively patterned children. A leaf stops
descent; every strict descendant reply is forced absent. At depth
$b$, choose alpha, beta, or a live symbol $z_{d,w}$ recording a
branch at that occurrence. Its eventual value must be a branch image.
The pair $(d,w)$ names that symbol, so different frontier occurrences
have independent names. This construction is finite: recursion has
bounded depth and three choices at each reached node. It enumerates
only consistent leaf-stopping patterns, rather than allowing an
independent absent label at a reached child of a branch.

Let $T_d$ be the resulting free term for class $d$. Both occurrences
of a repeated class in $\mathscr S(T)$ use exactly the same term
and symbols. Different live names need not have different values;
no equality or disequality of unobserved residuals is part of a
profile. The required negatives are exactly the whole-class list

$$
T_d\ne T_e\qquad(d,e\in D,\ d\ne e).
\tag{TCR.15}
$$

These are inequalities of entire terms, including every concrete
piece, not childwise inequalities. Expand any fixed ground pieces
in the ordered alpha/beta signature when testing syntax. Define

$$
\begin{aligned}
\operatorname{Im}(\alpha)&=\mathsf{false},&
\operatorname{Im}(\beta)&=\mathsf{true},&
\operatorname{Im}(z_{d,w})&=\mathsf{true},\\
\operatorname{Im}(\langle A,B\rangle)
&\Longleftrightarrow
 (A\text{ is literally }\beta\ \land\ B\text{ is literally }\alpha)
 \ \lor\ (\operatorname{Im}(A)\land\operatorname{Im}(B)).
\end{aligned}
\tag{TCR.16}
$$

Retain exactly the pattern tuples $\eta$ satisfying

$$
\operatorname{Im}(\mathscr S(T))
\quad\land\quad
\forall d\ne e,\quad T_d\text{ and }T_e
                    \text{ have different free syntax}.
\tag{TCR.17}
$$

Call this finite family $\Omega_b$. Its representation and tests are
the image-profile construction of PCA Definition 11.1 and Theorem
11.2, used here for the installed reader menu. No code-determining
certificate occurs in (TCR.14)–(TCR.17).

**Lemma 5.2 (simultaneous finite branch-image separation).** Let a
finite collection of free ordered alpha/beta terms have height at
most $h$, treating each variable as a leaf. For every finite
$L\ge0$, all its syntactically unequal term pairs can be kept unequal
by one assignment of finite branch images to the variables, each
with minimum leaf depth greater than $L$.

Proof. List the distinct variables $z_1,\ldots,z_m$. Let
$B_0=\beta$ and $B_{n+1}=\langle B_n,B_n\rangle$. Each $B_n$
is an image, by (TCR.3), and for $n\ge1$ it is a branch whose
leaves all have depth $n$. Assign $z_i=B_{N_i}$, where, for example,

$$
N_i=L+1+(h+1)(i+1)\qquad(1\le i\le m).
\tag{TCR.18}
$$

All $N_i$ exceed $h$ and $L$, are positive, and have pairwise
gaps greater than $h$. The height of an evaluated free term is the
maximum of the depths of its concrete leaves and of
$N_i+$ the depth of an occurrence of $z_i$. This follows by
induction on the free term.

Consider two different terms and descend through equal pair
constructors until the first syntactic mismatch. Unequal concrete
constructors remain unequal. Two different variables have different
assigned heights. It remains to compare a variable $z_i$ with a
nonvariable subterm $A$ of height at most $h$. If $A$ has no variable,
its evaluated height is at most $h<N_i$. Otherwise let $N_k$ be
the largest assigned height among its variables. If $N_k<N_i$,
the evaluated height is at most $\max(h,N_k+h)<N_i$. If
$N_k>N_i$, it is at least $N_k>N_i$. If $N_k=N_i$, $A$ has a
pair root and that variable occurs at positive depth, so its
evaluated height is greater than $N_i$. A literal-root $A$ cannot
contain a variable. These cases exclude equality at the mismatch.
Injectivity of the ordered pair constructor then excludes equality
of the original terms. The one assignment separates every listed
pair simultaneously. With no variables, the empty assignment suffices
for unequal ground terms. All assigned trees have the required
minimum leaf depth. $\square$

This elementary finite-term specialization supplies the simultaneous
filling needed here. PCA Theorem 11.2 already owns exact actual
image-profile attainment; no new general prescribed-rank filling
theorem is asserted.

**Proposition 5.3 (exact actual realization, including closed profiles).**
Let $\eta_b(u)$ be the tuple of actual class replies through depth
$b$, encoded as above. Then

$$
\Omega_b=\{\eta_b(u):u\in\mathcal U_*\}.
\tag{TCR.19}
$$

Moreover every retained profile, for every finite $L$, has an actual
finite origin realizing it with all its live symbols simultaneously
filled by branch images of minimum leaf depth greater than $L$,
and with all of (TCR.15) true. Every member of a profile has the
same replies at all installed Read words and the same entire target.

Proof. First, (TCR.16) is exact for image membership under every
assignment of branch images to its variables. Literal and variable
cases follow from (TCR.3). At a pair, the special block $E$ occurs
exactly when its children are literally beta and alpha: a variable
is a branch and a pair remains a branch, so neither can evaluate to
a literal leaf. The other image case is exactly that both children
are images. Induction on the free term proves the assertion,
including the whole exterior $\mathscr S(T)$.

Take any actual $u\in\mathcal U_*$. Its finite tree has a unique
prefix decomposition through depth $b$, stopping at every early
leaf. Every frontier branch subtree is an image by Definition 2.1.
Its actual values therefore constitute an assignment of the required
kind. Image membership implies the first test in (TCR.17). Identical
free class terms would evaluate equally under this assignment,
violating actual different-class disequality. Thus every actual
profile passes the second test as well, proving inclusion in
$\Omega_b$. Repeated occurrences use one class term and early
leaves account for every forced absent continuation.

Conversely fix a retained tuple. Apply Lemma 5.2 to its six class
terms and all their syntactically unequal pairs. It supplies one
simultaneous assignment, for any prescribed $L$, making every
whole-class negative true. The first test in (TCR.17) and exactness
of (TCR.16) put the filled $\mathscr S(x)$ in $\mathcal I$.
Each class term has precisely its recorded prefix: fixed constructors
are unchanged, a live frontier value is a branch, and nothing is
filled below a recorded leaf. Supplier 2.4's legal valuation and
inverse give the actual finite origin

$$
u_\eta=\delta(\mathscr S(x)),\qquad
\rho u_\eta=\mathscr S(x),\qquad R_P(\rho u_\eta)=R_*.
\tag{TCR.20}
$$

This realizes the exact profile and every original disequality.
If there are no live symbols, all terms are closed grounds; their
unequal syntax already gives the negatives and the empty assignment
works. Such a retained profile can have a single actual filling.
If a frontier branch is the only exposed constructor it may be
deepened, but a fully exposed $E$ remains that literal closed piece.
No accepted profile is assumed infinite, and no discarded candidate
can be an actual profile by the first inclusion.

Every installed hole suffix has length at most $b$. A recorded
leaf or its absent cone, a visible branch, or a frontier branch
therefore determines its exact reply. Exterior words have the fixed
branch reply. The roots in the same profile determine its unique
case in (TCR.8), so Supplier 2.4 fixes the entire target $R_h$ as
well. This proves the last assertion and both directions of
(TCR.19). $\square$

## 6. Table-only selection and an independently checkable certificate

**Definition 6.1 (finite response and bounded entry check).** For
$\eta\in\Omega_b$, let $v_\eta$ list the truthful replies at every
installed Read, including unused and duplicate states, as computed
from its pattern and the exterior. Let $h(\eta)\in\{0,1,2,3,4\}$
be its target index from (TCR.8). These are finite syntactic data.
For each $z\in\{0,1\}$ perform the following mathematical bounded
check on the fixed table and this response vector.

Start at $e_z$ with zero calls. If the state is a Halt, accept
exactly if its whole output equals $R_{h(\eta)}$. At a Read with
fewer than two calls used, use that state's coordinate of $v_\eta$,
take its fixed successor and increment the call count. Check for a
Halt again, including just after the second call. A Read still
present after two calls fails. A wrong Halt fails immediately.
The resulting set of accepted labels is denoted $\Gamma_T(\eta)$.
Whole-output equality compares finite exteriors, complete partitions,
canonical names and guards, rather than only a target label.

This check includes an initial Halt, early stopping, wrong outputs,
self-loops, longer cycles, a still-running second-call successor,
and behavior from either entry even if that entry is never prescribed
for a code on this profile. Repeated running visits still pay calls.
No correctness or termination of an unprescribed entry is assumed.

**Lemma 6.2 (exactness of the finite good-entry table).** For every
actual origin $u$,

$$
G_T(u)=\Gamma_T(\eta_b(u)).
\tag{TCR.21}
$$

Proof. Proposition 5.3 fixes every installed reply and the whole
target on that profile. From either identical entry, induction on
the at most two running visits gives identical states and identical
call counts for the bounded check and actual execution. A Halt's
fixed output is the same in both. A state still running at the
limit supplies no free Halt or decoder in either contract. Hence
their acceptances are equivalent for each label. This proves
(TCR.21) even for incorrect or nonterminating other-entry behavior.
$\square$

**Theorem 6.3 (effective table-only common-pair certificate).** Under
the nonempty-class promise, a terminating finite procedure whose
only nonpublic input is $T,e_0,e_1$ returns a pair $(j,z)$ satisfying
(TCR.12) and a finite certificate of that fact. It receives no
original code program, code values, source oracle or certificate
determining an original code.

Proof. Compute (TCR.14). Enumerate Definition 5.1's finite pattern
family, retain exactly the tuples passing (TCR.17), and compute for
each retained profile its installed response vector, target and both
bounded entry checks. Structural recursion decides the image test;
finite free syntax decides all whole-class negatives. There is no
test of a computation defining a code.

For each of the eight pairs in lexicographic order on
$J\times\{0,1\}$, test

$$
\Omega_b(j):=\{\eta\in\Omega_b:h(\eta)=j\}\ne\varnothing,
\qquad
\forall\eta\in\Omega_b(j),\quad\Gamma_T(\eta)=\{z\}.
\tag{TCR.22}
$$

Each test is finite. Every $\Pi_j$ is nonempty, and Proposition 5.3
shows that $\Omega_b(j)$ is exactly its family of attained profiles.
By Theorem 4.2 some pair has (TCR.12); actual realization of every
retained profile and (TCR.21) imply (TCR.22) for that pair. Thus the
scan selects a pair. Conversely, for any pair passing (TCR.22),
every $u\in\Pi_j$ has one of the scanned profiles and (TCR.21)
gives (TCR.12). The finite test is therefore both sound and complete
for this whole-fiber exclusive-entry property.

After checking all eight pairs, choose the first passing pair in the
fixed order. This makes the selection itself a function of the table
and its original entry labels alone.

One certificate contains $b$, the complete ordered retained profile
list and its six free terms per profile, its image and whole-class
syntax test data, all installed-state replies, the complete target
row per profile, the two bounded state paths with call counts and
acceptance results, and the selected pair. The explicit simultaneous
filling rule (TCR.18) may be included with each profile's height
bound; it provides finite ground witnesses without any source oracle.
The certificate contains no program, evaluation or determining
assignment for an original $\sigma$.

An independent finite verifier rebuilds the candidate patterns from
$b$, rechecks that $b$ is the installed maximum (TCR.14), and
recomputes exactly the retained list using (TCR.17). In particular
it checks exhaustive equality of the list, not just the validity
of listed samples. It recomputes all installed replies, all full
targets and both bounded runs, and checks (TCR.22). It can also
check that the chosen pair is the first passing pair. Proposition
5.3 proves that this exhaustive list misses no actual origin
profile and contains none without an actual inverse origin.
Lemma 6.2 then proves the verifier's conclusion for the entire
$\Pi_j$. A false profile list, omitted state, altered row or
incorrect entry path cannot establish that conclusion by these tests.

All recursions have bounded finite syntax, each simulation uses
at most two calls, and the last scan has eight candidates. Hence
both the construction and verification terminate. Their finiteness
asserts no useful complexity bound. The promise
$\mathcal C(T)\ne\varnothing$ is retained as a hypothesis; no
decision or certification of that promise is part of this procedure.
The chosen $\sigma_0$ in Theorem 4.2 is used only to prove existence
and is never queried or supplied to it. $\square$

## 7. One shared original-code-preserving root reader

**Theorem 7.1 (one table and one faithful map for the full code class).**
From the pair certified in Theorem 6.3, a finite table-only construction
specifies one representative-root reader $T^{\mathrm{root}}$ with
exactly nine installed states and one fixed injective entry map
$\iota^{\mathrm{root}}:\{0,1\}\to\mathcal K^{\mathrm{root}}$ such
that

$$
\forall\sigma\in\mathcal C(T)\ \forall u\in\mathcal U_*,\quad
T^{\mathrm{root}}\text{ from }
\iota^{\mathrm{root}}(\sigma(u))
\text{ returns the entire }F(u)\text{ within four paid calls}.
\tag{TCR.23}
$$

The table and map are chosen once, before selecting any particular
compatible code. The original value $\sigma(u)$ is preserved
pointwise on every original actual source.

Proof. Use the four-test construction of NRN Theorem 4.2's sufficiency
direction, now with the common certified pair. To specify all constants,
let $(i_1,i_2,i_3,i_4)$ be $j$ followed by the remaining indices in
increasing order. The exact installed words at the four Reads are

| Certified $j$ | $(i_1,i_2,i_3,i_4)$ | Literals at $(Q_1,Q_2,Q_3,Q_4)$ |
| --- | --- | --- |
| $1$ | $(1,2,3,4)$ | $(LLR,LRR,RLR,RRR)$ |
| $2$ | $(2,1,3,4)$ | $(LRR,LLR,RLR,RRR)$ |
| $3$ | $(3,1,2,4)$ | $(RLR,LLR,LRR,RRR)$ |
| $4$ | $(4,1,2,3)$ | $(RRR,LLR,LRR,RLR)$ |

Install four separate Reads $Q_1,Q_2,Q_3,Q_4$ and five separate
Halts $H_0,\ldots,H_4$. The complete Read table is

| Read | Literal | On alpha | On beta | On branch | On absent |
| --- | --- | --- | --- | --- | --- |
| $Q_1$ | $p_{b_{i_1}}$ | $H_{i_1}$ | $Q_2$ | $Q_2$ | $Q_2$ |
| $Q_2$ | $p_{b_{i_2}}$ | $H_{i_2}$ | $Q_3$ | $Q_3$ | $Q_3$ |
| $Q_3$ | $p_{b_{i_3}}$ | $H_{i_3}$ | $Q_4$ | $Q_4$ | $Q_4$ |
| $Q_4$ | $p_{b_{i_4}}$ | $H_{i_4}$ | $H_0$ | $H_0$ | $H_0$ |

The five fixed Halt entries are

| Halt | Fixed entire row, with all stored data of Definition 2.3 |
| --- | --- |
| $H_0$ | $R_0=(C_0,\pi_0)$, eight holes, name vector $(0,1,0,3,4,5,4,7)$, no absent cut |
| $H_1$ | $R_1=(C_1,\pi_1)$, name vector $(0,1,2,3,2,5)$, beta guard at $LL$ |
| $H_2$ | $R_2=(C_2,\pi_2)$, name vector $(0,1,2,3,2,5)$, beta guard at $LR$ |
| $H_3$ | $R_3=(C_3,\pi_3)$, name vector $(0,1,0,3,4,5)$, beta guard at $RL$ |
| $H_4$ | $R_4=(C_4,\pi_4)$, name vector $(0,1,0,3,4,5)$, beta guard at $RR$ |

These entries literally contain the full exteriors (TCR.6), partitions
(TCR.7), ordered holes, all different-class disequalities and all
blocked-cut data of Definition 2.3. The notation supplies no later
source-dependent decoder. Set once

$$
\iota^{\mathrm{root}}(z)=Q_1,
\qquad\iota^{\mathrm{root}}(1-z)=Q_2.
\tag{TCR.24}
$$

The two states are distinct; inverse labeling recovers the complete
bit at entry. There is no separate surviving bit register.

Fix any $\sigma\in\mathcal C(T)$ and any original actual $u$.
Each tested root is reached and is alpha exactly at its positive
index, if there is one, by Supplier 2.4. Entry $z$ tests all four
possible indices. Entry $1-z$ skips only $j$; (TCR.12) and
compatibility exclude this entry on every source of $\Pi_j$.
Thus every positive source reaches its own whole-row Halt from
its prescribed entry. On every $Z_d$ and $Z_*$ all right roots
are non-alpha, including a possible beta at a right class, and
both entries reach $H_0$. This covers every zero beta placement
and every allowed finite branch shape on the full domain. The
surviving repeated partner hole and all guards are already stored
in the chosen fixed output.

There are at most four actual invocations from $Q_1$ and at most
three from $Q_2$. All four successor constants at each Read are
installed, including absence, although these representatives are
reached. Every visit is a paid native call. All four Reads and all
five Halts count even if a particular code does not reach every
one. The ordering, entry map, addresses and transitions are static
output data, with no runtime address calculation, free control
step, phase, table selection or decoding state. Since the same
pair works for all compatible codes, the same installed table
and fixed map establish the quantifiers in (TCR.23). $\square$

**Remark 7.2 (a separately known singleton alphabet).** Outside the
two-call premise, if a code is known to attain only $z$, it is
identically $z$. The same four-root chain with that original bit
entered at $Q_1$ serves it faithfully; an unused second label can
be assigned $Q_2$ without altering a run. This does not relabel
the attained value. Proposition 3.4 proves that a singleton
alphabet is incompatible with the original full-fiber two-call
promise, so it is not a hidden extra assumption of Theorem 7.1.

## 8. Sharpness and the acquisition boundary

**Corollary 8.1 (inherited sharpness of the four-call guarantee).**
No universal conclusion of at most three calls within nine root
states can replace (TCR.23), and no universal eight-state root
conclusion can do so. These failures already occur for one lawful
code in the premise.

Proof. NRE Definition 8.2's code $\sigma^\dagger$ has the nine-state
arbitrary-literal two-call realization of NRE Theorem 8.4. NRE
Theorem 8.6 excludes every same-code root reader within nine states
and three calls; NRE Theorem 8.7 attains four calls within nine.
NRN Corollary 7.2 records exactly this inherited sharpness. Any
eight-state terminating root reader has at least five Halts for
the five complete outputs, hence at most three Reads. On one
stationary source a repeated Read repeats its deterministic suffix
forever, so a terminating run visits each Read at most once, as
in NBP Proposition 12.5 and NRN Lemma 4.1. Such a reader would
use at most three calls, contradicting the same NRE lower bound.
The canonical counterexample therefore refutes both stronger
universal conclusions. NBP Theorem 15.4's eight-state same-code
two-call normalization retains its smaller input budget; it does
not cover every nine-state premise here. $\square$

**Convention 8.2 (entry correctness does not generate an original code).**
PCA Theorem 8.2 exhibits a lawful acquired-term code served by one
fixed eight-state two-call reader but generated by no finite
stationary fixed-address common-start preparer on the entire
original fiber, even under sourcewise termination alone. Its
varying zero-fiber predicate inspects an entire acquired branch
image for an alpha leaf. PCA Theorem 15.2 gives a total,
finitely preparable program family sharing that fixed reader
for which no uniform extractor returns a determining depth,
determining menu or original-code preparer. These are inherited
statements, with their full promises and conclusions unchanged.

The input here is a finite installed bounded reader table with
its labeled entries. The finite profile determines which entries
return the whole target within two calls. It need not determine
which one an original code selects when both are correct. In
PCA Supplier application 4.3's fixed reader, both entries work
on $Z_{b_3}$: the zero entry's right chain returns $R_0$, and
the other entry tests $b_3=\beta$ and also returns $R_0$.
PCA's code template permits the bit there to depend on its
arbitrary lawful acquired-term predicate. Thus the same table
can serve different codes, including its nongenerable code,
while the table-only finite good-entry data stay the same.
An original code's determining assignment cannot be inferred
by treating a good-entry set as a selected bit.

Theorem 6.3 supplies a certificate of a shared positive-fiber
entry constraint. It does not supply PCA's determining
certificate for the entire original bit, a source-independent
preparer for it, or a procedure on arbitrary code-program text.
Theorem 7.1 still receives exactly the bit actually computed
and exported by its supplied producer. It does not acquire or
generate that bit. Hence it is compatible with both PCA
Theorems 8.2 and 15.2. Nor does it presume code-preserving
padding, which NBP Proposition 15.8 refutes: only the profile
realization proof changes hidden fills, and no original code
value is attributed to those changed sources.

## 9. Ownership, verification scope and remaining limits

**Convention 9.1 (inherited content and the precise added result).**
The supplier assignments are:

| Canonical numbered owner | Exact role |
| --- | --- |
| NBP Definitions 1.1–1.2 and 9.1; Propositions 9.3 and 15.2 | Native trees, four replies, full actual inverse fiber, legal valuations, image inverse, repetitions, all whole-class disequalities, eleven exhaustive profiles and five complete rows. |
| NBP Assumptions 9.2 and 10.6; Definitions 11.1 and 15.1; NRE Assumption 3.1 and Definition 3.2; NRN §3 | Acquired/exported prescribed code, complete access cut, faithful common entry, paid stationary service and every installed state and running visit charged. |
| NRN Theorem 6.1 | The per-code whole-positive-fiber obstruction (TCR.11), applied directly rather than reproved. |
| PCA Definition 11.1 and Theorem 11.2 | Finite image-profile representation, exact actual attainment and whole-term negative discipline; §5 exposes all needed realization details with an elementary simultaneous finite branch-image filling. |
| NRN Theorem 4.2, sufficiency direction | The four-right-root chain once a constant pair is available; §7 uses one common pair and one fixed faithful map for all compatible codes. |
| NRE Theorems 8.4, 8.6–8.7; NRN Corollary 7.2 | The inherited counterexample and sharp four-call boundary at nine states. |
| PCA Theorems 8.2 and 15.2 | Nongeneration and promised-program nonextraction boundaries, concerning the original complete code rather than correct-entry constraints. |

The additional deduction is Lemma 4.1's lawful finite-edit closure
and Theorem 4.2's common exclusive-entry fiber across the entire
fixed-table code class. Its effective consumer is Theorem 6.3:
the installed menu alone gives exact finite good-entry profiles,
an exhaustive sound and complete pair test and an independently
verifiable certificate. Theorem 7.1 combines this with the
inherited root chain to produce one table and one injective
entry map with the quantifier order in (TCR.23).

**Convention 9.2 (ordinary proof and realization limits).** The
profile enumeration, filling construction, bounded simulation,
verification and reader emission are terminating mathematical
procedures described in proofs. No enumeration, numerical
experiment, mathematical program or Lean proof has been run as
evidence for these results. Ordinary proof supplies the universal
claims; no finite sample is used to replace an actual full fiber.
No efficiency bound follows from termination or finite syntax.

The nonempty compatible-code class is a hypothesis. This volume
does not decide it, extract an original code program or its
determining certificate, classify all code programs, or provide
a program-wide compiler. The replacement preserves each original
bit pointwise, not the input table's state names, paths, replies,
two-call bound, address prices or acquisition/preparation budgets.
Changed cuts, source promises, extra updates or ports, source-bearing
entry fields, randomization, computed addresses and extra workspace
require new correspondences.

All installed abstract states and all actual reader invocations
are charged. Acquiring the current row and values, computing the
original bit, exporting it, isolating discarded material, lawful
new entry after absorbing stop, authentic stationary service,
installation, table and address representation, whole-output
storage, literal submission and local work retain separate prices.
The paper construction implements none of those supplied services
and certifies no physical memory, time, energy or empirical
machine-learning transfer. It makes no kernel-verification,
worldwide-originality or broader-programme completion claim.

[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[NRE]: FIB_PRESCRIBED_CODE_NINE_STATE_ROOT_ESCAPE.md
[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md

## 追加锚（本行以下为增补区）
