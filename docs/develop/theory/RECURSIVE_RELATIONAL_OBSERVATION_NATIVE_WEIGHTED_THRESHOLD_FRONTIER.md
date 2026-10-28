# Native weighted threshold frontier and common-history certificates

This companion studies the original prescribed-threshold preparation task
of [PCA, §§23–39][PCA] and the installed-table collisions of
[PE, §§1–6][PE]. It identifies its entire uniform resource feasibility
region with an unrestricted weighted Boolean graph problem, then proves
a necessary double-certificate obstruction on actual shared histories.

This is append-only generic-v1 mathematical reference input. The proofs
are ordinary paper mathematics, without Lean kernel verification,
executed mathematical checking, independent review acceptance or a
worldwide-priority claim. Mathematical authorship is by one Codex CLI
author using the formal-thinking-and-answer and theory-volume-template
skills within a paper-only scope. Existing source and classical results
retain the attribution given in §10. Corrections and extensions belong
after the final append anchor.

## 1. The unchanged original source, code and complete reader

**Definition 1.1 (actual full fiber).** Use the free algebra of all finite
nonempty ordered trees, with the original homomorphic update

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=E:=\langle\beta,\alpha\rangle,\quad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
\tag{WTF.1}
$$

Every finite original-root word in $\mathcal W=\{L,R\}^*$ is legal,
including $\varepsilon$. Its reply is alpha, beta, branch or absent;
descent beyond a leaf is absent. Equal subtrees at different addresses
retain their distinct occurrences.

Fix $P=\{L,R\}^3$ and the complete current row $R_*$ with the perfect
depth-three exterior and equality classes

$$
\{LLL,LRL\}=a,\quad \{LLR\}=b_1,\quad \{LRR\}=b_2,\quad
\{RLL,RRL\}=c,\quad \{RLR\}=b_3,\quad \{RRR\}=b_4.
\tag{WTF.2}
$$

Every two different classes assert whole-subtree disequality. A complete
row retains the ordered exterior, all reached occurrence holes, their
whole equality partition and all concrete strict-prefix blocking guards.
Canonical class names are recomputed from first occurrences after any
restriction. The domain and whole predecessor target are exactly

$$
\mathcal U_*=\{u\in\mathcal T:R_P(\rho u)=R_*\},\qquad F(u)=R_P(u).
\tag{WTF.3}
$$

There is no bound on size, height or hidden interior shape. For an
injective six-class valuation $x$, write its actual current filling as

$$
\mathscr S(x)=
\left\langle
 \left\langle\langle x_a,x_{b_1}\rangle,
                  \langle x_a,x_{b_2}\rangle\right\rangle,
 \left\langle\langle x_c,x_{b_3}\rangle,
                  \langle x_c,x_{b_4}\rangle\right\rangle
\right\rangle.
\tag{WTF.4}
$$

The inherited image grammar is
$\mathcal I=\rho[\mathcal T]=\{\beta,E\}\cup
\{\langle y,z\rangle:y,z\in\mathcal I\}$.
Its three parsing cases are disjoint because alpha is not an image.
The actual inverse is
$\delta(\beta)=\alpha$, $\delta(E)=\beta$, and
$\delta\langle y,z\rangle=\langle\delta y,\delta z\rangle$
for image children. It obeys $\rho\delta=\mathrm{id}$ on $\mathcal I$
and $\delta\rho=\mathrm{id}$ on $\mathcal T$.

By [TMC, (RA.2207)][TMC] and [NBP, Proposition 9.3][NBP],
$\mathscr S(x)$ is an image exactly when all six values are images,
or exactly one right-class value $x_{b_j}$ is alpha, its repeated
left partner is beta, and every other value is an image. All
different-class disequalities remain imposed. The actual origin is
$\delta(\mathscr S(x))$; the inverse is a proof supplier, not a controller
operation.

The exhaustive eleven profiles of [NBP, Proposition 15.2][NBP] are
$\Pi_j$, where $b_j$ is alpha, its partner is beta and all other roots
are branches; $Z_d$, where only class $d$ is beta and the other roots
are branches; and $Z_*$, where all six roots are branches. Unspecified
branch values range over all allowed finite branch images. The five
literal complete predecessor outputs are $R_0=R_*$ on all zero profiles
and $R_j$ on $\Pi_j$. For
$(q_1,q_2,q_3,q_4)=(LL,LR,RL,RR)$, $R_j$ replaces only the two sibling
holes at $q_jL,q_jR$ by concrete beta at $q_j$, retaining the remaining
exterior and restricting the entire old partition canonically. The other
occurrence of the repeated partner remains an old hole. Every surviving
disequality and every blocking guard is part of the output.

**Definition 1.2 (the fixed pointwise code).** Let $n\ge3$,
$A=\{s_1<\cdots<s_n\}$ be distinct positive original positions,
$1\le k\le n$, and $r\ge0$. Set

$$
w_i=L^{s_i}R,\quad a_i=LLLw_i,\quad c_i=|a_i|=s_i+4,\quad
C_B=\sum_{i\in B}c_i,\quad W=C_{[n]}.
\tag{WTF.5}
$$

For every finite branch image $B$, define
$\theta_i(B)=\mathbf1_{\{r_B(w_i)=\mathsf{branch}\}}$.
All three other replies, including absence, contribute zero. Keep the
original function, without reselection or recoloring:

$$
\sigma_{A,k}(u)=
\begin{cases}
0,&u\in\Pi_1\cup\Pi_2,\\
1,&u\in\Pi_3\cup\Pi_4,\\
\mathbf1_{\{\sum_i\theta_i(x_a)\ge k\}},&u\in Z_{b_3},\\
0,&u\text{ is in any other zero profile}.
\end{cases}
\tag{WTF.6}
$$

This is [PCA, Definitions 4.2 and 23.1][PCA] on the identical
$\mathcal U_*$. It specifies a function on acquired finite data; those
data are not an input to the paid preparer.

**Convention 1.3 (literal complete entries and separate reader).**
Keep exactly the reader fixed by [PCA, Supplier application 4.3 and
Convention 23.2][PCA], using [NBP, Theorem 15.5][NBP] with
$z=0$, positive codes $(0,0,1,1)$ and distinguished test $3$.
Its complete entries are the original distinct $e_0,e_1$, with their
original recoverable labels. Write $i_1,i_2$ for the fixed order of
$\{1,2\}$ in its zero-entry chain. Its three running states have the
following inherited form; $H_j$ is the halt bearing the entire $R_j$.

| Reader state | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $e_0$ | $q_{i_1}R$ | $H_{i_1}$ | $H_0$ | $Q_2$ | $H_0$ |
| $Q_2$ | $q_{i_2}R$ | $H_{i_2}$ | $H_0$ | $H_0$ | $H_0$ |
| $e_1$ | $RLR$ | $H_3$ | $H_0$ | $H_4$ | $H_0$ |

These are the fixed entries, table and whole outputs, not new choices.
The five different whole-row halts and all three running states count
in its separate $K=8$. Its fresh costs are $q_R\le2$, $\ell_R\le6$.
Preparation must terminate at the literal latch
$\widehat e_{\sigma_{A,k}(u)}$, and code-only handoff enters that same
complete state on that same actual register. Returning merely $F(u)$,
or substituting a different usable code, is insufficient.

**Definition 1.4 (native feasibility).** A preparer has one finite
installed set consisting of running states, the two original-entry
latches and all $r$ further mandated distinct latches. A running state
has one fixed absolute word and four fixed successors. There is one
source-independent running start and no silent running transition.
Its sole changing configuration is its counted current state. It must
terminate correctly on every $u\in\mathcal U_*$. Count all installed
states, including unused states and unused latches. Every running visit
costs one invocation and its actual word length, including constants,
roots, absence, repeated words and visits after a threshold certificate.

For integers $H,p,L$, let $\mathsf N_{A,k,r}(H,p,L)$ mean existence of
such a preparer with at most $H$ installed states and, simultaneously,

$$
q_P(u)\le p,\qquad \ell_P(u)\le L
\quad\text{for every }u\in\mathcal U_*.
\tag{WTF.7}
$$

Any negative resource bound means infeasible. Arbitrary stationary
sharing, repeated variables and union-graph cycles remain admitted.
Only each actual source run must terminate. There is no free
source/target/history archive, counter, phase, reset, work register,
computed address, source copy, subtree, equality or inverse port.

**Assumption 1.5 (separate services).** The original update and register
binding, same-version row acquisition and authentication, pre-cut native
permission, actual export, complete access isolation, paid code-only
handoff, lawful complete entry and stationary truthful native service
remain separately supplied as in PCA Assumptions 1.2 and 33.2 and PE
Assumption 1.4. The current source remains fixed throughout both phases.
Table and address representation, installation, entry and whole-output
contents, local acquired-term work, service storage, physical memory,
time and energy have their separate prices. None is inferred from a
Boolean cube or from a finite table's mathematical existence.

## 2. Actual-source suppliers for the resource correspondence

**Supplier 2.1 (simultaneous cube and all addresses).** Reuse [PCA,
Lemma 24.1][PCA]. There are actual finite origins
$u_\theta\in Z_{b_3}$ for every $\theta\in\{0,1\}^n$, all with
whole target $R_0$, with prescribed bit
$\mathbf1_{\{|\theta|\ge k\}}$. Every finite word is cube-constant or
depends injectively on just one bit, precisely at the disjoint sets

$$
E_i=\{p w_i z:p\in\{LLL,LRL\},\
                      z\in\{\varepsilon,L,R\}\}.
\tag{WTF.8}
$$

At the two occurrence roots the bit replies are beta/branch; at their
children they are absent/beta, in bit order zero/one. Every $E_i$ word
has length at least $c_i$, with equality just at the occurrence roots.

For clarity, the supplied actual realization uses
$G=\langle\beta,\beta\rangle$, $C_0=G$,
$C_{M+1}=\langle C_M,\beta\rangle$, $M\ge s_n$.
In $C_M$, replace the beta at $w_i$ by $G$ just when $\theta_i=1$,
obtaining the branch image $B_\theta$. The selected words are prefix-free.
Choose fixed pairwise distinct branch images $D_c,D_1,D_2,D_4$ avoiding
all these finitely many $B_\theta$, and set

$$
x_a=B_\theta,\quad x_c=D_c,\quad x_{b_3}=\beta,\quad
x_{b_j}=D_j\ (j=1,2,4),\qquad
u_\theta=\delta(\mathscr S(x)).
\tag{WTF.9}
$$

The image supplier proves actual feasibility, both partner repetitions
and all six-class disequalities. Replacement changes only the selected
root and its two children; deeper replies there are absent in both
cases, and proper prefixes remain branches. The occurrence identity

$$
r_{\rho u}(p v)=r_{x_{[p]}}(v)\qquad(p\in P,\ v\in\mathcal W)
\tag{WTF.10}
$$

of NBP (NBP.9.7) therefore covers every finite word, including all
unselected cones and leaf extensions. This is a lower-witness family;
no shape or depth promise is placed on an upper construction.

**Lemma 2.2 (mandatory charge on every cube run).** For every correct
native preparer and every cube vector, its complete actual run has a
nonselected invocation of length at least three. Also its installed
table has two running states outside $\bigcup_iE_i$ with different
words in the disjoint cones $RLR\mathcal W$ and $RRR\mathcal W$.
Consequently, if $M$ is its total installed selected-state count,

$$
H_P\ge M+4+r.
\tag{WTF.11}
$$

Proof. This reuses the all-weight comparison in the proof of PE Theorem
3.1, with its parameter range unnecessary for this comparison. For a
negative $\theta$, keep $B_\theta$ and $D_1,D_2,D_4$, replace $x_c$
by beta and $x_{b_3}$ by alpha. This actual $\Pi_3$ origin has code
one, with all selected replies unchanged. For a positive $\theta$,
replace only $x_{b_3}=\beta$ by a fresh branch image avoiding all other
class values. This actual $Z_*$ origin has code zero, again with
unchanged selected replies. In both cases distinctness, repeated
occurrences and the exterior before depth three persist. If the cube
run never queried a distinguishing word, its comparison source would
follow the same fixed successors to the same entry. Correctness forbids
this. A distinguishing invocation on that very cube run is nonselected
and has length at least three. This proves a charge on each run
separately, with no summation over comparison sources.

For the installed-state assertion reuse PCA Lemma 7.1, as exposed in
PE Theorem 4.2. Choose $x_c=\beta$ and pairwise distinct branch images
at the other five classes. This actual $Z_c$ source has code zero.
Replacing only $x_{b_3}$ by alpha gives an actual $\Pi_3$ source of
code one, differing only in the $RLR$ cone; hence some installed word
in that cone is necessary. Replacing instead only $x_{b_4}$ by alpha
gives the analogous necessity in the $RRR$ cone. The cones are disjoint
from each other and from all selected words. Add the two original-entry
latches and all $r$ mandated latches. Unused installed states still
count, proving (WTF.11). $\square$

A fixed-source terminating stationary run never revisits the same
running state: its fixed reply and successor would repeat its entire
suffix forever. This inherited principle, PCA Lemma 2.3 and NBP
Proposition 12.5, does not prohibit cycles in the union of different
actual paths, or repeated coordinates at different installed states.

## 3. The unrestricted weighted Boolean problem

**Definition 3.1 (Boolean feasibility and terminal convention).**
A Boolean graph has $m_B$ installed running states, two distinct output
terminals $0,1$, one source-independent running start, one fixed
$i(v)\in[n]$ and two fixed successors at every running state. The whole
changing configuration is the current state. On input
$\theta\in\{0,1\}^n$, a visit reads $\theta_{i(v)}$, costs one query
and $c_{i(v)}$ letters, then follows its fixed zero/one successor.

Every installed running state counts, including unreachable ones.
Every actual visit counts, including repeats after certification.
Require semantic termination and output
$\mathbf1_{\{|\theta|\ge k\}}$ on every input. Impose no variable
order, read-once, leveling, graph-path-realizability or union-acyclicity
condition. A syntactic graph path assigning opposite values to one
coordinate need not be an actual path.

Let $\mathsf B_{c,k}(m,t,J)$ mean existence with $m_B\le m$ and uniform
query and weighted-letter upper bounds $t,J$ on every Boolean input.
Any negative bound means infeasible. The parameter $m$ counts running
states only: the Boolean total installed alphabet has $m_B+2$ states.
Both terminals will become two counted native entry latches. Thus the
native overhead beyond $m_B$ is two profile states plus two terminals
plus $r$ latches; it is not an additional four states beyond the
Boolean total.

**Lemma 3.2 (simultaneous Boolean execution floors).** Every such total
Boolean threshold graph has one actual input on which it reads all $n$
different coordinates. Its uniform bounds therefore satisfy

$$
t\ge n,\qquad J\ge W.
\tag{WTF.12}
$$

Proof. Answer first exposures by one until $k-1$ ones have been given,
then by zero. Repeated queries retain their old values. Before the
$n$th distinct exposure, fewer than $k$ ones and at most $n-k$ zeros
have been seen, so both outputs remain possible. The graph cannot
terminate there correctly. Nor can it repeat a running state: all
answers on the intervening segment have been fixed, and any completion
would then loop on that actual input. Finiteness of the installed graph
forces eventual progress to all $n$ exposures. Complete the resulting
assignment to its actual input; the same induction follows its path.
That one path pays at least $n$ queries and $\sum_i c_i=W$ letters.
This is an existence proof by consistent replies, not an executed
enumeration. $\square$

## 4. Exact native and weighted-Boolean feasibility

**Theorem 4.1 (the entire original uniform frontier).** For Definition
1.2's parameters and every integer triple $(H,p,L)$,

$$
\boxed{\quad
\mathsf N_{A,k,r}(H,p,L)
\ \Longleftrightarrow\
\mathsf B_{c,k}(H-4-r,\ p-1,\ L-3).
\quad}
\tag{WTF.13}
$$

The native quantifier is over the entire unbounded original fiber.
The Boolean model is exactly Definition 3.1, with paid repeats and
arbitrary stationary sharing. This is an equivalence of simultaneous
uniform upper-budget feasibility.

Proof, projection. Start with a native witness and its actual runs on
Supplier 2.1's cube. Retain one Boolean running state for each original
selected state reached on at least one cube input, labeled $i$ when its
word is in $E_i$. The two outputs retain their original zero/one labels.
At an occurrence root use its beta/branch successors as Boolean
zero/one successors; at a selected child use absent/beta instead.

Bypass cube-constant states along their unique constant-reply
successors, both from the old common start and after each realized
selected edge. Such a realized chain is finite: a cube source realizing
its incoming edge follows that whole constant chain, so a constant-state
loop would contradict its actual termination. It reaches another retained
selected state or the appropriate original-entry latch. The initial
chain must reach a selected state, since otherwise every cube input
would reach the same latch despite the nonconstant threshold.

For a selected edge not realized by any cube input at its original
state, give its Boolean successor any terminal. This defines a total
static graph even if the unused original continuation loops or reaches
an unused state. It does not assert that the unused edge is realizable.
For each fixed $\theta$, induction from the common start follows
exactly the selected-state subsequence of the old run on its one actual
$u_\theta$. At each induction step its outgoing edge is realized by
that same source, so no newly assigned impossible edge becomes
reachable. The projected graph is correct and terminates on every
Boolean input. No graph unfolding or leveling has occurred.

Its installed running-state count is at most the original $M$, hence
at most $H-4-r$ by Lemma 2.2. On each input its query count is precisely
the number of selected visits of the old cube run. Its weighted charge
is at most those visits' actual total length, since every $E_i$ word
has length at least $c_i$. Its own old complete cube run separately
contains the additional invocation of Lemma 2.2. Therefore

$$
q_B(\theta)+1\le q_P(u_\theta)\le p,\qquad
L_B(\theta)+3\le\ell_P(u_\theta)\le L.
\tag{WTF.14}
$$

These inequalities retain every repeated selected-coordinate visit.
They prove Boolean feasibility at all three stated bounds together.

Proof, full-fiber lift. Conversely take any qualifying Boolean graph.
Install every one of its running states at the fixed native literal
$a_{i(v)}=LLL L^{s_{i(v)}}R$, retaining even its unused states. Replace
its terminals by the original $\widehat e_0,\widehat e_1$. At each
running state install the Boolean-one successor for branch, and
separately install the Boolean-zero successor for alpha, beta and
absent. This is a fixed four-reply table, with no running indicator
calculation, counter or computed address.

Add the following two different profile states, start at $D$, and
install all $r$ additional mandated latches:

| Native state | Literal | alpha | beta | branch | absent |
| --- | --- | --- | --- | --- | --- |
| $D$ | $RLR$ | $\widehat e_1$ | Boolean start | $T$ | $\widehat e_0$ |
| $T$ | $RRR$ | $\widehat e_1$ | $\widehat e_0$ | $\widehat e_0$ | $\widehat e_0$ |

On every actual $u\in Z_{b_3}$, its arbitrary branch image $x_a$
defines the static vector $\theta_i(x_a)$ of Definition 1.2. The
all-address occurrence identity (WTF.10) makes each actual selected
visit exactly that Boolean bit test under the installed four successors.
Thus semantic termination and threshold correctness hold for every
such branch image, including noncomb images, alpha replies and absent
selected nodes. No vector, inverse or archive is given to the apparatus.

The full profile partition proves correctness elsewhere. Alpha at $D$
means $\Pi_3$ and latches one. Beta means precisely $Z_{b_3}$. When
$D$ returns branch, the only remaining code-one profile is $\Pi_4$,
detected by alpha at $T$; every other such profile requires zero.
All four root successors are installed even when absence is unreachable.
This exhausts every source in $\mathcal U_*$, and produces literally
its original prescribed complete entry. The unchanged reader of
Convention 1.3 then returns that same source's entire predecessor row,
with repeated occurrences, canonical partition, disequalities and
blocking guards. Nothing in the lift changes a source or a target.

The installed preparation count is exactly $m_B+4+r$. On a selected
route the two charged coordinates are exactly

$$
q_P(u)=1+q_B(\theta(x_a)),\qquad
\ell_P(u)=3+L_B(\theta(x_a)).
\tag{WTF.15}
$$

Other routes have at most two calls and six letters. Lemma 3.2 forces
$p-1\ge n$ and $L-3\ge W$ whenever the Boolean premise is feasible.
Since $n\ge3$ and $c_i\ge5$, these budgets dominate those other routes.
Thus the lifted preparer fits the original $(H,p,L)$ simultaneously.
The separate reader's eight states and fresh calls are unchanged.

Finally, if a bound on either side is negative, its stated feasibility
is false. If a shifted bound is negative while native bounds are
nonnegative, the projection inequalities and (WTF.11) exclude a native
witness as well. This covers all integer triples. $\square$

**Corollary 4.2 (uniform normalization with the original code).**
Every finite correct native preparer admits a profile-first,
selected-root-only preparer with no larger installed-state count or
uniform call and letter maxima, and the identical pointwise original
code and complete entries on all sources.

Proof. A terminating stationary finite table has finite maxima, by the
no-revisit principle in §2. Apply both constructions of Theorem 4.1 at
those maxima and its installed count. The resulting table has exactly
the profile front and selected literals displayed there. $\square$

This comparison is uniform. For a particular arbitrary $u$, the proof
compares its normalized selected route to the old run on
$u_{\theta(x_a)}$, not necessarily to the old run on that same $u$.
It asserts neither pointwise path preservation nor
$q_{\rm new}(u)\le q_{\rm old}(u)$ or
$\ell_{\rm new}(u)\le\ell_{\rm old}(u)$ for each original source.
The code itself is pointwise unchanged. The selected graph remains
unrestricted, so this is not a read-once or grid normalization.

## 5. The original installed-state minima remain symbolic

**Corollary 5.1 (the exact remaining Boolean objectives).** For
$2\le k\le n-1$, use the original $H_{\mathrm{exec}}(A,k;r)$ and
$H_{\min}(A,k;r)$ of PCA Definition 32.2. Let $b(n,k)$ be the minimum
running-state count of a total stationary Boolean threshold graph with
no execution caps. Then

$$
\begin{aligned}
H_{\mathrm{exec}}(A,k;r)
 &=4+r+\min\{m:\mathsf B_{c,k}(m,n,W)\},\\
H_{\min}(A,k;r)&=4+r+b(n,k).
\end{aligned}
\tag{WTF.16}
$$

In particular, unrestricted $H_{\min}$ is independent of the actual
positive selected positions $A$ at fixed $(n,k,r)$. No independence of
$H_{\mathrm{exec}}$ from the weights, and no new numerical optimum, is
asserted.

Proof. The first equation is Theorem 4.1 at the original simultaneous
caps $p=n+1$, $L=3+W$. For the second, every finite total Boolean
graph has finite uniform query and weighted maxima, since each fixed
input terminates and there are finitely many inputs. With no execution
caps, changing positive $c_i$ changes those finite prices but not
which graphs compute the threshold or their installed count. Minimize
Theorem 4.1 over the finite feasible budgets. The finite grid of PCA
Theorem 26.1 supplies nonempty sets of feasible cardinalities, so these
integer minima exist. Its supplier, not this identification, supplies
the already established numerical special cases. $\square$

Writing $G=k(n-k+1)$, strict original subgrid feasibility under both
execution caps is therefore equivalent to a Boolean graph with fewer
than $G$ installed running states, at most $n$ queries and weighted
charge at most $W$. The existence of such a graph, or a general lower
bound forbidding it, is not proved by (WTF.16).

## 6. Actual live-history geometry at both execution caps

**Convention 6.1 (scope and supplied live facts).** In §§6–9 let
$n\ge6$, $3\le k\le n-2$, and let $P$ be any original native
preparer correct on the whole $\mathcal U_*$ with, on every source,

$$
q_P\le n+1,\qquad \ell_P\le3+W.
\tag{WTF.17}
$$

A cube history includes every invocation already made and ends just
before its next invocation. Let $S$ be its exposed coordinate set,
$\eta_S$ its old bit assignment, $h$ its exposed ones, and
$z_S=|S|-h$ its exposed zeros. It is live exactly when
$h<k$ and $z_S\le n-k$, or $1\le k-h\le n-|S|$.
Every completion of its old bits is an actual cube source following
that history, by Supplier 2.1 and deterministic induction.

Reuse the following exact suppliers. PCA Theorem 34.3 forces each
selected invocation from a live history to be a fresh shortest
occurrence-root query. The only live nonselected word is $RLR$,
at most once in a live portion. Every live history has negative and
positive saturated completions of weights $k-1,k$; they read every
coordinate once at its root and their one further call is $RLR$ before
their last selected query, followed directly by the appropriate latch.
PE Lemma 4.1 excludes properly nested exposed sets and different
supports with equal hits at a common running state. PCA Theorem 35.1
excludes equal supports with unequal hits and gives the interval
exclusion used next. These are statements about actual histories,
not labels assigned to shared nodes.

**Notation 6.2 (one incomparable collision).** Suppose two actual live
histories reach one original installed selected state, with incomparable
supports $S,T$ and hits $h<g$. Put

$$
\begin{gathered}
I=S\cap T,\quad X=S\setminus T,\quad Y=T\setminus S,\quad
U=[n]\setminus(S\cup T),\\
a=|X|>0,\quad b=|Y|>0,\quad u=|U|,\quad
q=k-h,\quad v=k-g,\quad \Delta=g-h=q-v,\\
\xi=|\{i\in X:\eta_S(i)=1\}|,\qquad
\eta=|\{i\in Y:\eta_T(i)=1\}|,\\
D_I=\{i\in I:\eta_S(i)\ne\eta_T(i)\},\qquad
\delta=\Delta+\xi-\eta.
\end{gathered}
\tag{WTF.18}
$$

Every set and count here is a proof index, never an accessible register.
The next selected coordinate must be fresh for both histories, hence
belongs to $U$; in particular $u\ge1$.

The supplied interval exclusion is

$$
[0,u]\cap[q-b,q-1]\cap[v-a,v-1]\cap\mathbb Z=\varnothing.
\tag{WTF.19}
$$

Its two clipped intervals are nonempty by liveness. Their upper
endpoints are ordered because $q>v$. Disjointness therefore places the
$v$ interval strictly below the $q$ interval. The latter's lower
endpoint is positive, hence $q-b$, and the former's upper endpoint is
below $u$, hence $v-1$. This recovers PE (PE.6):

$$
q\ge b+1,\qquad v\le u,\qquad \Delta\ge b.
\tag{WTF.20}
$$

Moreover $\delta$ is the difference of old hit counts on $I$, namely
$(g-\eta)-(h-\xi)$. Since

$$
\delta=(\Delta-b)+\xi+(b-\eta)\ge0,
\tag{WTF.21}
$$

equality means precisely $\Delta=b,\ \xi=0,\ \eta=b$.
Thus every private-polarity defect, meaning $\xi>0$ or $\eta<b$,
has $\delta>0$.

## 7. Common-old-coordinate re-distinguishing and two certificates

**Theorem 7.1 (actual common-suffix certificate packing).** Use Convention
6.1 and Notation 6.2, and suppose $\delta>0$. Define

$$
\lambda=b+u-q+1,\qquad
J=\{t\in\mathbb Z:\max(0,v-\xi)\le t\le\min(u,q-\eta-1)\}.
\tag{WTF.22}
$$

Then $\lambda,v$ are positive and $J$ is nonempty. For every assignment
$\omega\in\{0,1\}^U$ of weight $t\in J$, there are two actual cube
sources completing the respective histories, agreeing outside $I$,
with original prescribed entries $e_0,e_1$.

Their suffixes from the common state have a first different native
reply, at one original installed state with fixed word
$a_*\in E_i$ for some $i\in D_I$. Just before that invocation, the two
actual histories have already acquired respectively a negative and a
positive cube-threshold certificate. This invocation is a paid requery
of a coordinate old on both histories.

Write $X_1=\{i\in X:\eta_S(i)=1\}$ and
$Y_0=\{i\in Y:\eta_T(i)=0\}$, and let $U_0,U_1$ be the zero and one
sets of $\omega$. Before that first different reply, the common suffix
contains shortest-root certificate calls at disjoint sets

$$
C_-\subseteq Y_0\cup U_0,\quad |C_-|=\lambda,\qquad
C_+\subseteq X_1\cup U_1,\quad |C_+|=v.
\tag{WTF.23}
$$

These calls together with the first differing call occupy
$\lambda+v+1$ distinct original installed selected states and obey

$$
\begin{aligned}
\lambda+v+1&\le u+\min(a,b),\\
C_{C_-}+C_{C_+}+|a_*|&\le C_U+\min(C_X,C_Y).
\end{aligned}
\tag{WTF.24}
$$

The certificate statement concerns the cube threshold; it need not
discharge all original-profile obligations or perform the actual entry.

Proof. Liveness gives $q\le b+u$, so $\lambda\ge1$, and $v\ge1$.
Since $\delta>0$, integrality gives $v-\xi\le q-\eta-1$.
By (WTF.20) and $\eta\le b$, the right endpoint before clipping is
nonnegative, and $v-\xi\le u$. Hence clipping both to $[0,u]$
leaves a nonempty integer interval.

Fix any allowed $\omega$. On both sources put the old $S$ values on
$X$, the old $T$ values on $Y$, and $\omega$ on $U$. On $I$ keep
the respective history's own values. The resulting vectors, denoted
$\theta^-,\theta^+$, each extend their own actual history, differ only
on $D_I$, and have weights

$$
|\theta^-|=h+\eta+t\le k-1,\qquad
|\theta^+|=g+\xi+t\ge k.
\tag{WTF.25}
$$

Supplier 2.1 realizes each as a genuine finite original source. Every
old constant and selected reply in its own incoming history is
unchanged, so each reaches the same original shared state as stipulated.

From that state, identical actual replies give identical fixed
successors. If no reply ever differed, termination would give the same
literal entry on both sources, contradicting (WTF.25). There is a first
different reply at a common running state. The complete all-address
classification places its word in $E_i$ for $i\in D_I$: every other
coordinate and every cube-constant word has the same reply. In
particular $D_I\ne\varnothing$.

That coordinate was exposed on both histories before the shared state.
If either history were still live immediately before this requery,
the live freshness supplier would prohibit that very invocation.
Both are therefore nonlive. Exposures cannot remove a genuine
certificate, and their final signs are respectively zero and one.
Thus the negative source has exposed at least $n-k+1$ zeros and the
positive source at least $k$ ones before the requery.

Initially the negative history had $|S|-h$ zeros. It needs precisely

$$
(n-k+1)-(|S|-h)=b+u-q+1=\lambda
\tag{WTF.26}
$$

new zeros for its first negative certificate. Take their first
exposures. They are in $Y_0\cup U_0$, since these are the zeros outside
$S$ on that source. Each is queried while that source is still live,
including the exposure completing its certificate, and therefore at
a shortest occurrence root of length $c_i$. Similarly take the $v$
first new one exposures completing the positive source's first positive
certificate. They lie in $X_1\cup U_1$ and are shortest-root calls.
All occur before the first different reply and so are on one common
state sequence. A zero and a one outside $I$ cannot have the same
coordinate, as the sources agree there. This proves (WTF.23).
Their coordinates are distinct and outside $I$, whereas $a_*$ reads
$I$, proving the asserted distinct installed-state count. In addition,
sourcewise termination keeps the requery state distinct from its
earlier prefix state on each source.

Every prefix leading to an initially live history is itself live.
Consequently those two incoming prefixes contain respectively $|S|$
and $|T|$ selected calls with charges exactly $C_S,C_T$.
Lemma 2.2 applies separately to each completed source even at these
nonsaturated final weights. Each complete run therefore has at most
$n$ selected visits and at most $W$ selected letters. The selected
calls just identified give, separately,

$$
\begin{array}{ll}
|S|+\lambda+v+1\le n,&
C_S+C_{C_-}+C_{C_+}+|a_*|\le W,\\
|T|+\lambda+v+1\le n,&
C_T+C_{C_-}+C_{C_+}+|a_*|\le W.
\end{array}
\tag{WTF.27}
$$

Other calls can only consume further budget. Now
$n-\max(|S|,|T|)=u+\min(a,b)$ and
$W-\max(C_S,C_T)=C_U+\min(C_X,C_Y)$.
These are exactly (WTF.24). Taking the tighter of two same-source
constraints does not add costs of different sources. The compulsory
nonselected invocation can lie before the common state, inside the
common suffix, or after its first different reply; no common timing
assumption was used. $\square$

## 8. Absolute-cost and omission consequences

**Corollary 8.1 (a usable weighted collision test).** For a coordinate
set $B$, let $L_j(B)$ be the least $C_F$ among its $j$-element subsets,
with $L_0(B)=0$ and $L_j(B)=+\infty$ when none exists. For each allowed
$\omega$ in Theorem 7.1, necessarily

$$
L_\lambda(Y_0\cup U_0)+L_v(X_1\cup U_1)
       +\min_{i\in D_I}c_i
\le C_U+\min(C_X,C_Y).
\tag{WTF.28}
$$

Proof. Lower-bound each actual certificate charge in (WTF.24) by its
defining minimum, and use $|a_*|\ge c_i$ at the first differing word.
Thus a single violating allowed $\omega$ excludes that actual collision.
The actual word in (WTF.24) can be a longer selected child; its extra
letter is never free. $\square$

**Corollary 8.2 (per-source payment for the common-old requery).**
On each of the two complete actual runs in Theorem 7.1 separately, let
$D$ be its exposed coordinate set, $m_j$ its number of $E_j$ visits,
and $O=[n]\setminus D$ its omitted coordinates. Put

$$
R=\sum_{j\in D}(m_j-1),\quad
R_c=\sum_{j\in D}(m_j-1)c_j,\quad
E_{\rm sel}=\sum_{\text{selected visits in }E_j}(|a|-c_j).
\tag{WTF.29}
$$

Let $N$ and $L_{\rm out}$ be that run's nonselected visit count and
letter charge. Then

$$
|O|\ge R+N-1,\qquad
C_O\ge R_c+E_{\rm sel}+L_{\rm out}-3.
\tag{WTF.30}
$$

In particular it omits at least one coordinate and $C_O\ge c_i$ for
its first distinguishing coordinate $i\in D_I$.

Proof. Exact accounting gives
$q_P=|D|+R+N$ and
$\ell_P=C_D+R_c+E_{\rm sel}+L_{\rm out}$.
Use the two caps, $E_{\rm sel}\ge0$, and Lemma 2.2's $N\ge1$,
$L_{\rm out}\ge3$. Since $i$ was old before the common state and is
queried again, $m_i\ge2$ and $R\ge1,\ R_c\ge c_i$. These are
separate full-run identities, not a transfer of slack between sources.
$\square$

**Corollary 8.3 (unit common-hit-gap price).** If $\delta=1$, put
$t=v-\xi=q-\eta-1\in[0,u]$, $Y_1=Y\setminus Y_0$,
$X_0=X\setminus X_1$, and $c_*=\min_{i\in D_I}c_i$. Then

$$
c_*\le
\min\{C_{Y_1}+L_t(U),\ C_{X_0}+L_{u-t}(U)\}.
\tag{WTF.31}
$$

Proof. Here the cross-filled sources have weights exactly $k-1,k$.
On a weight-$k-1$ cube source every zero coordinate must be exposed
before a correct entry: flipping an unexposed zero changes the
prescribed entry while keeping every preceding actual native reply.
Dually a weight-$k$ source must expose every one. The omitted
coordinates in the first run are therefore contained in
$Y_1\cup U_1$, and in the second in $X_0\cup U_0$, since their old
supports were already exposed. Corollary 8.2 gives
$c_*\le C_{Y_1}+C_{U_1}$ and
$c_*\le C_{X_0}+C_{U_0}$ for every $t$-one assignment on $U$.
Minimize these two necessary inequalities separately. The assignments
minimizing them need not coincide; no joint attainment is claimed.
$\square$

## 9. General hit/zero separation and the original whole-table consumer

**Theorem 9.1 (two-coordinate separation at a shared original state).**
Suppose two actual live histories at one original installed selected
state have different pairs of exposed hit and zero counts. Orient their
hits as $h<g$. This orientation is always possible, and necessarily

$$
g-h\ge2,\qquad z_S-z_T\ge2.
\tag{WTF.32}
$$

Proof. Different pairs cannot have both equal supports and equal hits.
Equal supports with different hits are excluded by PCA Theorem 35.1;
different supports with equal hits and all properly nested supports
are excluded by PE Lemma 4.1. Thus they have incomparable supports and
different hits, and Notation 6.2 applies after orientation.

If $\delta>0$, the first inequality of (WTF.24) and
$\lambda+v+1=b+u-\Delta+2$ give

$$
\Delta\ge2+\max(0,b-a).
\tag{WTF.33}
$$

Therefore $\Delta\ge2$ and
$z_S-z_T=\Delta+a-b\ge2$.

If $\delta=0$, (WTF.21) gives $\Delta=b,\xi=0,\eta=b$.
Both one-sided hypotheses of PE Theorem 3.1 now apply to this very
collision, forcing $a=b$ and $C_X=C_Y$. Their nonempty disjoint
private sets cannot both be singletons, because original selected
positions have distinct individual costs. Hence $a=b=\Delta\ge2$,
and the zero-count difference is the same $\Delta$. This proves both
inequalities without a subset-sum nonresonance assumption. $\square$

**Proposition 9.2 (a strict obstruction for every interior parameter).**
For every $n\ge6$, $3\le k\le n-2$, every original $A$ and $r$,
partition coordinates with

$$
|I|=n-k,\qquad X=\{x\},\quad Y=\{y\},\qquad |U|=k-2.
\tag{WTF.34}
$$

Consider an $S=I\cup X$ history with all $I$ bits zero and $x=1$,
and a $T=I\cup Y$ history with exactly two ones on $I$ and $y=0$.
These are actual live histories obtainable in a full-domain original
preparer obeying both caps. They cannot reach the same original
selected state in any such preparer. The exclusion is additional to
PE's interval and one-sided private-polarity conditions.

Proof. The supports have the same size. Their hits are $h=1,g=2$,
and their zero counts are $n-k,n-k-1$. Both are live, since $k\ge3$.
Their nonempty common unread set is $U$. Both private polarity
hypotheses fail: the old $X$ bit is one and the old $Y$ bit is zero.
Their two clipped intervals from (WTF.19) are respectively
$\{k-2\}$ and $\{k-3\}$, so the existing interval exclusion does not
rule them out; neither does PE Theorem 3.1. They are not equal-hit
or nested-support pairs, and PE Corollary 4.3's defect-free extreme
hypothesis is absent.

For actual occurrence of these prefixes, take a full Boolean query
tree reading all coordinates once. First read $I$ in a fixed order.
In the all-zero branch next read $x$; in a branch with exactly two
ones on $I$ next read $y$. At the respective resulting nodes choose
the same member of $U$ as next query, and finish each tree path by
fixed installed tests of its remaining coordinates. Every vertex has
a fixed label; no running count or selector is added. Attach threshold
terminals and apply the full-fiber lift of Theorem 4.1. Each selected
path pays exactly $n$ calls and $W$ letters, preceded by $D$; all other
profiles use its original two-state front. Supplier 2.1 gives actual
origins for both prefixes and every completion. This construction
only witnesses that the proposed incoming histories are lawful; it
claims no installed-state improvement.

If they shared a selected state, their hit difference one would
contradict Theorem 9.1. More explicitly, their parameters are
$a=b=1,\ u=k-2,\ q=k-1,\ v=k-2,\ \xi=1,\ \eta=0,\ \delta=2$.
Here $\lambda=1$, and (WTF.24) would require
$k\le k-1$. Thus any continuation identifying these histories violates
the original caps or correctness, for every set of original absolute
costs. This is a uniform parametric obstruction, not a list of
small-cardinality optima. $\square$

**Corollary 9.3 (strengthened necessary condition for a smaller table).**
Let $G=k(n-k+1)$. If an original full-domain preparer obeying both caps
has $H<G+4+r$, then two of its actual live histories at an original
selected state come from different pairs

$$
0\le h\le k-1,\qquad 0\le z\le n-k.
\tag{WTF.35}
$$

Their differences obey (WTF.32). With Notation 6.2, either
$\delta=0,\ \Delta=a=b\ge2,\ C_X=C_Y,\ \xi=0,\ \eta=b$,
or $\delta>0$ and every conflict-band completion obeys the actual
double-certificate, cost and omission constraints of §§7–8.
Under PE (PE.11), the latter alternative is compulsory.

Proof. PE Theorem 4.2 chooses one actual live history ending just before
a selected invocation for each of the $G$ hit/zero pairs, and uses
$H\ge M+4+r$ to force two representatives to share an original
selected state. Equal-hit and nested cases are excluded as in Theorem
9.1. Apply that theorem and the $\delta=0$ characterization in its
proof. For $\delta>0$ use Theorem 7.1 and its consequences. PE (PE.11)
forbids equal sums on nonempty disjoint equal-size private sets,
excluding the first alternative. $\square$

This is a condition on every proposed smaller whole original table.
Proposition 9.2 supplies an entire excluded mixed-polarity class that
the older necessary tests leave available. Conversely compatibility
with these conditions does not construct a smaller table. In the
existing PE Theorem 5.1 family, the hit and zero gaps are both $m+1$,
so the separation is consistent with that supplied sharing. Its
$m=1$ case realizes the two-gap boundary; it remains above the grid,
with its paid old-coordinate state $J$, and is not a new upper here.

The states counted in Theorem 7.1 are distinct on its one paired
suffix and on each of its actual runs. No global injection assigns a
different additional installed state to each collision. A requery state
can serve several collisions and can be a live query on another source.
Thus summing these local charges as new states would be unsupported.
Neither a no-larger read-once/grid replacement nor a general net-saving
or grid-optimality theorem follows. The still-open objective is exactly
the unrestricted weighted Boolean objective in (WTF.16), or equivalently
the unchanged original native objective.

## 10. Attribution, comparison and remaining boundaries

**Attribution 10.1 (supplied and derived mathematics).**

| Source | Exact role |
| --- | --- |
| TMC Proposition 22.2, (RA.2207) | Disjoint image grammar, actual inverse and injectivity |
| NBP Definitions 1.1–1.2 and 9.1, Propositions 9.3, 9.4 and 15.2, (NBP.9.7), Theorem 15.5 | Full original fiber, complete rows and guards, repetitions and disequalities, exhaustive profiles, all-address occurrence identity and the fixed complete-entry reader |
| PCA Definitions 1.1–2.2, 4.1–4.2, 23.1 and Convention 23.2; Lemmas 2.3, 7.1 and 24.1 | Original paid task, literal entries, stationary no-revisit, installed profile overhead and actual all-address cube |
| PCA Theorems 26.1, 34.3 and 35.1; Definition 32.2 | Existing full-domain grid, live saturation and interval exclusions, original installed-state objectives |
| PE Theorem 3.1, Lemma 4.1 and Theorem 4.2 | All-weight actual-source comparison, one-sided private charges, nested/equal-hit exclusions and the original-table collision consumer |
| PE Theorem 5.1 and Proposition 5.2 | Supplied mixed-private sharing, paid old-coordinate separator and failure of unconditional private balance even with distinct subset sums |
| This volume, Theorem 4.1 and Corollaries 4.2 and 5.1 | Source-specific exact weighted frontier, uniform original-code normalization and symbolic objectives |
| This volume, Theorem 7.1, §§8–9 | Actual common-old re-distinguishing, double-certificate packing, prices, general hit/zero separation and the all-parameter whole-table obstruction |

The two proofs here use one shared native contract. Generic deterministic
path contraction, threshold adversaries, certificate sensitivity and finite
minima are mature tools; they are not claimed as newly invented results.
The additional content is the exact source-specific bidirectional
resource map and the shared-history composition with its stated consumer.

PCA Theorems 12.4 and 14.3 already give general finite paid native-word
tasks with the same original budgets. They retain a certificate basis
or all budget-bounded original words and their attained profiles.
Theorem 4.1 instead proves the selected-bit projection with exact
$(4+r,1,3)$ offsets and the independent whole-fiber lift.
NBP §§12–14 allow jointly chosen usable encoders in their shared-table
correspondences; they do not preserve an independently prescribed
pointwise $\sigma$ automatically. [BPS, Theorem 9.1 and Convention
11.3][BPS] explicitly distinguishes SAME-budget SOME-code existence
from such pointwise preservation. Those results remain credited within
their own scopes.

[PPF, Definition 1.2 and Proposition 7.1][PPF] uses a bounded
late-target source family $\mathcal F_D=\{\langle\alpha,v\rangle:
\operatorname{ht}v\le D\}$ disjoint from $\rho[\mathcal T]$; its
literal-resource $H$ is a peak submitted length. [LTR, §§9–14][LTR]
has its own late-target/count order and retained-alphabet refinement
objectives. Their source, timing and resource coordinates are not
substitutes for this full-fiber installed preparation count.
The arithmetic source and randomized hard-two-request accuracy targets
of [Unequal Two-Tail Frontier, §1][UTT] likewise have no supplied
same-source/action/price map to this prescribed native task.

**Comparison 10.2 (primary branching-program references).** Ingo Wegener,
The Complexity of Boolean Functions, Chapter 14 §4, Definition 4.1
and Theorems 4.1 and 4.3, printed pp. 423–425 [WBP], supplies the
classical read-once symmetric grid and optimal residual count.
Printed p. 424 explicitly states that every graph path is realized
for BP1 and that this fails for general branching programs.
Bryant, Graph-Based Algorithms for Boolean Function Manipulation,
§2 Definition 1 [BRY], requires strict increase of variable indices
on every edge to a nonterminal.

Our selected state maps to one actual Boolean test, its $E_i$ reply
map gives the Boolean edge, and its literal contributes at least $c_i$;
the reverse map installs the precise original root and all four
successors. These maps prove Theorem 4.1. They do not prove read-once,
a fixed increasing order or realization of every syntactic path.
Accordingly no BP1 or ordered numerical lower bound is imported.

Rakesh Kumar Sinha, Some Topics in Parallel Computation and Branching
Programs, §2.1.3, printed p. 17 [SINHA], distinguishes semantic paths
from inconsistent graph paths and allows union cycles with no semantic
cycle. His stated leveling transformation takes $(l+1)s$ states by
copying each state $l+1$ times. Semantic termination matches our actual
input paths; that copying is not an installed-cardinality-preserving
transformation. Repeated-scan native consumers of classical upper
constructions already belong to PCA §§29–33, with their own larger
execution budgets. They do not determine the objective at $(n,W)$.

The cited primary passages are literature-attested for those restricted
models and semantic conventions. The exact native correspondence and
certificate obstruction are repo-derived ordinary deductions with the
proofs above. Bounded source and literature comparisons do not assert
worldwide novelty or that no other applicable theorem exists.

**Boundary 10.3 (unresolved original questions).** No numerical general
$H_{\mathrm{exec}}$ or $H_{\min}$, strictly subgrid attaining table,
global collision-to-state injection, or no-larger whole-table grid
replacement is proved here. General net saving remains open. Separate
acquisition, authentication, export, isolation, lawful entry, stationary
continuity and physical prices remain Assumption 1.5's obligations.
The exact reduction concerns uniform resource bounds; it does not
supply a new per-original-source cost domination or a physical
implementation. These finite paper results are progress on the
original unrestricted task, not satisfaction of the persistent research
goal.

[PCA]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PRESCRIBED_CODE_ACQUISITION.md
[PE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PRIVATE_EXCHANGE.md
[NBP]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_BIRTH_PROVENANCE.md
[TMC]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[BPS]: FIB_BOUNDED_NATIVE_PREPARER_SYNTHESIS.md
[PPF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PREPARATION_FRONTIERS.md
[LTR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_ONE_READ_MEMORY.md
[UTT]: FIB_NATIVE_UNEQUAL_TWO_TAIL_ATTAINED_FRONTIER.md
[WBP]: https://eccc.weizmann.ac.il/resources/pdf/cobf.pdf
[BRY]: https://www.cs.cmu.edu/~bryant/pubdir/ieeetc86.pdf
[SINHA]: https://dada.cs.washington.edu/research/tr/1995/08/UW-CSE-95-08-02.pdf

## 追加锚（本行以下为增补区）

## 11. Fixed-history separator capacity and representative choices

**Definition 11.1 (parameters, cells and certificate packs).** Fix an
integer $M\ge2$ and put

$$
n=3M+5,\qquad k=M+4,\qquad
[n]=\{t\}\sqcup X\sqcup Y\sqcup R\sqcup
       \{u_1,\ldots,u_M,v_1,\ldots,v_M\},
\tag{WTF.36}
$$

where $X=\{x,x'\}$, $Y=\{y,y'\}$ and
$R=\{r_1,\ldots,r_M\}$. Set
$U_j=\{u_{M-j+1},\ldots,u_M\}$ and
$I_j=[n]\setminus(X\cup Y\cup U_j)$, for $1\le j\le M$.
Use original costs $c_i=s_i+4$ with distinct positive integer positions
$s_i$, and assume the four inequalities of PE (PE.16):

$$
c_t\le c_{x'},\qquad c_t\le c_{y'},\qquad
c_x+c_t\le C_Y,\qquad c_y+c_t\le C_X.
\tag{WTF.37}
$$

One permitted input is $c_i=5\,3^{i-1}$, $s_i=c_i-4$, with
$t,x,y,x',y'$ at indices $1,2,3,4,5$, and the other coordinates
assigned the remaining indices in the displayed order. Its five costs
are $5,15,45,135,405$, so (WTF.37) holds. The positions are strictly
increasing and positive. Its subset sums are distinct: the greatest
term at which two subsets differ exceeds the sum of all earlier terms.
This is the permitted input choice of PE Proposition 5.2 extended to
$n$ coordinates; after fixing it the pointwise code of Definition 1.2
is held fixed.

For a table of Definition 3.1 at caps $(n,W)$, write

$$
\mathcal D_{n,k}=\{(h,z):0\le h\le k-1,\ 0\le z\le n-k\}.
$$

A live-cell representative system chooses, for each cell in
$\mathcal D_{n,k}$, an actual live history with those exposed one and
zero counts, ending before a running invocation. Its state map is
$f:\mathcal D_{n,k}\to Q_B$, where $Q_B$ is the installed running
set. The chosen histories are part of the system. A collision is a
pair of distinct cells with the same representative state; a collection
of collisions is cell-disjoint when no cell belongs to two pairs.
This uses the representative notion in PE Theorem 4.2, without
requiring $f$ to be injective or a state to determine a residual.

For fixed colliding histories satisfying Theorem 7.1, an allowed
completion means its exact cross-fill: retain each history's own $I$
values, use the old $S$ values on $X$ and old $T$ values on $Y$ on
both inputs, and choose any $\omega$ in its conflict band on $U$.
Its first separator is the first common-suffix state with different
replies. Its certificate pack consists of that state and the first
new zero and one exposures completing the two certificates in
(WTF.23). In the collisions below $\lambda=v=1$, so this is an
unambiguous three-state pack. Here $v$ denotes the residual count of
Notation 6.2, not a coordinate $v_i$.

**Definition 11.2 (one complete table with a retained separator).**
Start with a complete binary query tree of depth $n$, with different
running vertices at all internal positions, and terminal $0$ or $1$
at depth $n$ according to the full threshold. Every path queries every
coordinate exactly once, including after a certificate. First query
$r_1,\ldots,r_M$ in that order. The notation $e_j$ in a routing vector
means the $j$th unit vector, distinct from the reader entries $e_0,e_1$.

In the cylinder $R=e_j$, query $t$ next, then all of
$I_j\setminus(R\cup\{t\})$ in increasing coordinate-index order.
If $t=0$, query $x,x'$ next; if $t=1$, query $y,y'$ next.
Finish by increasing index among the remaining coordinates.
In $R=0^M$, use increasing index among the remaining coordinates
except that $t$ is last. In every other routing cylinder use increasing
index among all remaining coordinates. These rules assign a fixed
coordinate to each distinct tree vertex.

Select the following two prefixes in $R=e_j$. On the low prefix put
$t=0$, all old $u_i$ equal to zero, $v_1,\ldots,v_{M-j}$ equal to
one and the remaining $v_i$ equal to zero, then $(x,x')=(1,0)$.
On the high prefix put $t=1$, all old $u_i$ equal to zero, all
$v_i$ equal to one, then $(y,y')=(0,1)$. Empty displayed lists impose
no conditions. Their supports are respectively $I_j\cup X$ and
$I_j\cup Y$, and both have length $n-j-2$.

In the untouched cylinder $R=0^M$, retain the final $t$-vertex after
all $v_i$ and $x,x',y$ have answered one, and all $u_i$ and $y'$
have answered zero. Call this existing vertex $J$. Its prefix has
$M+3=k-1$ ones, so its zero and one successors are $0,1$.

Delete the complete remaining subtree at each of the selected low and
high prefixes, including its root. Each has $j+2$ query levels.
Redirect both incoming edges at scale $j$ to a new vertex $V_j$.
Install the following distinct new scan states; the state $J$ in their
successors is the existing vertex just retained.

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $V_1$ | $u_M$ | $B_X$ | $B_Y$ |
| $V_j$, $2\le j\le M$ | $u_{M-j+1}$ | $Z_{M-j+2}$ | $O_{M-j+2}$ |
| $Z_i$, $2\le i<M$ | $u_i$ | $Z_{i+1}$ | $J$ |
| $O_i$, $2\le i<M$ | $u_i$ | $J$ | $O_{i+1}$ |
| $Z_M$ | $u_M$ | $B_X$ | $J$ |
| $O_M$ | $u_M$ | $J$ | $B_Y$ |

Install four further distinct private states, disjoint from the tree
and all scan states:

| State | Coordinate | Zero successor | One successor |
| --- | --- | --- | --- |
| $B_X$ | $x$ | $B_{x'}$ | $J$ |
| $B_{x'}$ | $x'$ | $0$ | $1$ |
| $B_Y$ | $y$ | $J$ | $B_{y'}$ |
| $B_{y'}$ | $y'$ | $0$ | $1$ |

All other retained tree transitions remain unchanged. The two original
Boolean terminals are the only terminals. Denote this installed table
by $B_M$. The shared scan and private transitions reuse the motif of
PE Theorem 5.1, but all scales here share their scan tails and the
single retained $J$.

**Theorem 11.3 (whole-table feasibility, exact count and native lift).**
The table $B_M$ is total, terminates correctly on every Boolean input,
and has exact installed running count

$$
m_B=2^{3M+5}-16(2^M-1)+5M+1>G=k(n-k+1).
\tag{WTF.38}
$$

Every input uses at most $n$ queries and weighted charge at most $W$;
one untouched input attains both bounds. The full-fiber lift of
Theorem 4.1 therefore has exact installed preparation count and
simultaneously attained uniform maxima

$$
H=m_B+4+r,\qquad p=n+1,\qquad \ell=3+W.
\tag{WTF.39}
$$

It preserves the entire original domain, code, literal complete reader
entries and separate reader of §1.

Proof. The unit routing cylinders are disjoint. Within a cylinder the
two selected prefixes differ at $t$, so their deleted subtrees are
disjoint too. Every deletion is below routing depth $M$ and is disjoint
from $R=0^M$. In particular it does not remove $J$.

The low prefix has $1+(M-j)+1=M-j+2=k-j-2$ hits. Its unread
set is $Y\cup U_j$, of size $j+2$, and its residual is AND on that
set. The high prefix has $1+1+M+1=M+3=k-1$ hits, unread set
$X\cup U_j$, and residual OR on that set. All these prefixes are live.
The scan sends an all-zero $U_j$ to $B_X$, an all-one $U_j$ to $B_Y$,
and a mixed $U_j$ to $J$ at its first change of value.

For a mixed scan the low AND is zero and the high OR is one, exactly
the respective old $t$ replies at $J$. On an all-zero scan the low
history has old $x=1$, so $B_X$ goes through $J$ to zero. The high
history obtains $x\lor x'$: if $x=1$ it goes through $J$ to one,
and if $x=0$ it reads $x'$. On an all-one scan the low history
obtains $y\land y'$: if $y=0$ it goes through $J$ to zero, and if
$y=1$ it reads $y'$. The high history has old $y=0$, so it goes
through $J$ to one. These six cases cover every assignment extending
either replaced prefix. Every other input follows the original
complete threshold tree. The scan index strictly advances, its exits
have at most two further calls, and $J$ terminates. The retained tree
also terminates. Thus every input has a correct finite run.

A replaced run has $n-j-2$ prefix calls, at most $j$ scan calls and
at most two tail calls, hence at most $n$ calls. The two prefixes
cost $C_{I_j}+C_X$ and $C_{I_j}+C_Y$, and the scan costs at most
$C_{U_j}$. The exhaustive tail charges are

| Scan exit | Low-prefix tail charge | High-prefix tail charge |
| --- | --- | --- |
| all zero | $c_x+c_t\le C_Y$ | $\max(C_X,c_x+c_t)=C_X$ |
| all one | $\max(C_Y,c_y+c_t)=C_Y$ | $c_y+c_t\le C_X$ |
| mixed | $c_t\le C_Y$ | $c_t\le C_X$ |

Here the two maximum equalities use $c_t\le c_{x'}$ and
$c_t\le c_{y'}$, respectively; the mixed inequalities follow from
these as well. Thus each complete replaced run costs at most
$C_{I_j}+C_X+C_Y+C_{U_j}=W$. Repeated $x,y,t$ calls and every
postcertificate call are included in these sums. Every untouched
$R=0^M$ input still queries all $n$ coordinates once, paying exactly
$n,W$ on that same run.

The complete tree contributes $2^n-1$ running vertices. Delete exactly
$2\sum_{j=1}^M(2^{j+2}-1)$ distinct vertices. Add $M$ states $V_j$,
$2(M-1)$ states $Z_i,O_i$, and four private states, or $3M+2$
in all. The existing $J$ is counted once in the retained tree and
is not added. Consequently

$$
\begin{aligned}
m_B&=(2^n-1)-2\sum_{j=1}^M(2^{j+2}-1)+(3M+2)\\
   &=2^n-16(2^M-1)+5M+1.
\end{aligned}
$$

This counts every installed vertex, including unnecessary complete-tree
vertices after certification. The retained zero-routing subtree alone
has $2^{n-M}-1=2^{2M+5}-1$ vertices. Since $2^M\ge M+1$,
its count is at least $32(M+1)^2-1$, strictly exceeding
$G=2(M+4)(M+1)$. This proves the strict inequality in (WTF.38).

Apply exactly Theorem 4.1, rather than placing a shape promise on the
upper domain. Each coordinate state installs the original absolute
literal $a_i=LLL L^{s_i}R$, with the one successor for branch and
three separately installed zero successors for alpha, beta and absent.
Retain every Boolean running state. Add its two profile states $D,T$
at $RLR,RRR$, its two literal original-entry latches and all $r$
mandated distinct latches, including unused ones. The all-vector proof
above applies to the static selected replies of every finite branch
image, not only the comb witnesses. The eleven profiles in §1 supply
all remaining sources. Supplier 2.1 supplies actual cube origins for
the untouched cap-attaining inputs, so the lift attains both (WTF.39)
maxima on one actual source.

The domain is exactly $\mathcal U_*$ of (WTF.3), with the original
$\rho$ and no size or depth bound. Every finite absolute address and
all four replies retain their original meaning. Both occurrences of
each repeated class, all different-class disequalities, the canonical
restricted partitions and every blocking guard remain in the complete
predecessor outputs. Handoff enters literally the unchanged COMPLETE
$e_0$ or $e_1$ on that same register. Convention 1.3's separate
$K=8$ reader, including every whole-row halt, is unchanged.
All actual native invocations, including root, constant, absent, repeated
and postcertificate calls, are paid as in Definitions 1.4 and 3.1.
The construction grants no source copy, archive, equality, inverse,
source-dependent selector, counter, computed address or additional
control port. Assumption 1.5's acquisition, authentication, export,
isolation, handoff, lawful entry, binding and continuity services
remain separately supplied and priced. $\square$

**Theorem 11.4 (one forced separator for every fixed-history completion).**
For each $j=2,\ldots,M$, keep exactly Definition 11.2's displayed low
and high histories at $V_j$. They represent the live cells

$$
L_j=(k-j-2,n-k),\qquad
H_j=(k-1,n-k-j-1).
\tag{WTF.40}
$$

All $2(M-1)$ cells are distinct. Cross-fill $(x,x')=(1,0)$ and
$(y,y')=(0,1)$ on both inputs. Every assignment on $U_j$ belongs
to Theorem 7.1's conflict band, and for every such assignment the first
differing common-old state is the same installed $J$ of Definition
11.2. In particular, for every joint choice
$(\omega_j)_{j=2}^M\in\prod_{j=2}^M\{0,1\}^{U_j}$, all $M-1$
first separators are that one $J$.

Proof. The hit counts were computed in Theorem 11.3. Subtracting them
from prefix length $n-j-2$ gives respectively $n-k$ and
$n-k-j-1$ zeros. All counts lie in $\mathcal D_{n,k}$, and both
residuals are nonconstant. Within either list the varying coordinate
makes the cells distinct, while every $L_j$ has fewer than $k-1$
hits and every $H_j$ has exactly $k-1$. Their hit and reverse-zero
gaps are both $j+1$, consistent with Theorem 9.1.

Their common old set is $I_j$, the private sets are precisely $X,Y$,
and their common unread set is $U_j$. Notation 6.2 specializes to

$$
a=b=2,\quad u=j,\quad q=j+2,\quad v=1,\quad
\xi=\eta=1,\quad \Delta=\delta=j+1,\quad \lambda=1.
\tag{WTF.41}
$$

Thus the band (WTF.22) is the entire integer interval $[0,j]$.
If $w=|\omega|$, the two cross-filled total weights are

$$
|\theta^-|=k-j-1+w\le k-1,\qquad
|\theta^+|=k+w\ge k.
\tag{WTF.42}
$$

Each extends its own fixed prefix and agrees with the other outside
$I_j$, so Supplier 2.1 realizes both as actual inverse origins.

Before leaving the scan both runs read identical $U_j$ bits. A mixed
assignment goes directly to $J$. An all-zero assignment goes through
$B_X$, whose common $x=1$ reply goes to $J$. An all-one assignment
goes through $B_Y$, whose common $y=0$ reply goes to $J$.
These are all assignments. No $v_i$, or any other differing coordinate
of $I_j$, is queried on this suffix before $J$. At $J$ the old
$t$ replies differ, zero on the low history and one on the high.
Thus this is the first different reply and is a paid requery on both
runs. In the native lift its literal is $a_t$ and its replies on
these actual origins are beta and branch.

The conclusion holds separately for each $j$ and every allowed
$\omega$. Taking their finite product proves the joint statement;
no compatibility between different inputs' completions is required.
As $M$ grows these are arbitrarily many cell-disjoint fixed-history
collisions with the same unavoidable first separator. The statement
does not quantify over other choices of the incoming histories.
$\square$

**Proposition 11.5 (favorable representatives on the same table).**
The table $B_M$ also admits an injective live-cell representative map
$f_{\rm good}$ whose image consists entirely of retained original-tree
vertices.

Proof. For $(h,z)\in\mathcal D_{n,k}$ put $d=h+z\le n-1$.
If $d\le M$, choose a prefix of the routing tree with $h$ ones and
$z$ zeros, and take its vertex at depth $d$. Every such vertex is
retained, since the deletions start at depths $n-j-2>M$.

If $d>M$ and $h\ge2$, set exactly $a=\min(h,M)$ routing bits to
one, taking the first $a$ for definiteness. There are enough routing
zeros: $M-a\le z$, since either $a=M$ or $d>M$ and $a=h$.
The routing vector has at least two ones, so its whole cylinder is
untouched. In the next $d-M$ positions of its fixed remaining order,
put $h-a$ ones and $z-(M-a)$ zeros. These counts are nonnegative
and sum to $d-M$, so the complete tree contains that prefix.

If $d>M$ and $h=0$ or $1$, use $R=0^M$. Here $z\ge M$.
In its next $d-M$ positions put $h$ ones and $z-M$ zeros. There
are enough positions and this cylinder too is untouched. In all cases
the resulting vertex is running because $d<n$, has the required
counts and is live. Its preceding prefixes are live as well, since
neither count can exceed its final live value. Actual cube completions
realize each chosen history.

Different cells cannot select the same retained vertex: its unique
inherited tree prefix has one fixed pair of exposed counts. Thus the
map is injective. This is an existence assertion on $B_M$, distinct
from allowing arbitrary representatives to be fixed in advance.
$\square$

**Proposition 11.6 (a fixed representative image with no external pack
candidate).** There is one lawful live-cell representative system $f$
on $B_M$ choosing both cells $L_j,H_j$ at $V_j$ for all $j\ge2$,
with the following two properties.

First, for $\omega_j$ having its sole one at $u_M$, the packs are
exactly $\{V_j,Z_M,J\}$, and all these packs lie in $\operatorname{im}f$.
Second, for the one fixed collision $L_2,H_2$, every allowed completion
has its entire pack in that same image. More precisely:

| $(u_{M-1},u_M)$ | Exact pack |
| --- | --- |
| $(0,0)$ | $\{V_2,B_X,J\}$ |
| $(0,1)$ | $\{V_2,Z_M,J\}$ |
| $(1,0)$ | $\{V_2,O_M,J\}$ |
| $(1,1)$ | $\{V_2,B_Y,J\}$ |

Consequently, writing $P_2(\omega)$ for these packs,

$$
\bigcup_{\omega\in\{0,1\}^{U_2}}
       \bigl(P_2(\omega)\setminus\operatorname{im}f\bigr)
=\varnothing.
\tag{WTF.43}
$$

Proof. The following five distinct live cells have the indicated
actual representative histories, in addition to all (WTF.40):

| State | Live cell | History reaching it |
| --- | --- | --- |
| $Z_M$ | $(k-1,n-k-2)$ | high $j=2$ prefix, then $u_{M-1}=0$ |
| $O_M$ | $(k-3,n-k)$ | low $j=2$ prefix, then $u_{M-1}=1$ |
| $B_X$ | $(k-1,n-k-1)$ | high $j=2$ prefix, then $U_2=(0,0)$ |
| $B_Y$ | $(k-2,n-k)$ | low $j=2$ prefix, then $U_2=(1,1)$ |
| $J$ | $(k-1,n-k)$ | untouched zero-routing prefix defining $J$ |

For the first and third rows start with high cell
$H_2=(k-1,n-k-3)$ and add respectively one or two fresh zeros.
For the second and fourth start with low cell
$L_2=(k-4,n-k)$ and add respectively one or two fresh ones.
The fifth prefix was specified in Definition 11.2. Every resulting
cell is live and is realized by actual cube completions. The first,
third and fifth have $k-1$ hits and zero counts $n-k-2,n-k-1,n-k$;
the other two have $k-3,k-2$ hits and $n-k$ zeros. They are pairwise
distinct. They also avoid (WTF.40): its low hits are at most $k-4$,
and its high zero counts are at most $n-k-3$.

Choose these five representatives and the displayed $2(M-1)$
collision histories simultaneously. For every other cell use the
history constructed in Proposition 11.5. The distinct cell assignments
are consistent and give one lawful full system $f$, as also permitted
by the general representative construction in PE Theorem 4.2.

For a one-hot-at-$u_M$ completion with $j\ge2$, $V_j$ first reads
a zero and completes the negative certificate, because the low
prefix already has $n-k$ zeros. The zero scan reaches $Z_M$ without
an intervening one. There $u_M=1$ completes the high history's
positive certificate, since it started with $k-1$ hits. The next
state is $J$. This proves the first claimed pack and its containment.

For $j=2$, an initial zero at $V_2$ completes the negative certificate;
an initial one completes the positive certificate. If $U_2=00$,
the first new positive hit is $x=1$ at $B_X$. If $U_2=01$, it is
$u_M=1$ at $Z_M$. If $U_2=10$, the first new negative zero is
$u_M=0$ at $O_M$. If $U_2=11$, it is $y=0$ at $B_Y$.
Theorem 11.4 supplies the same first separator $J$ in all four cases.
These identify the exact first-exposure packs, not just subsets of
longer paths. Their states all belong to the chosen image, proving
(WTF.43). Containment for every full pack at every $j$ is not
asserted; the all-completion assertion of Theorem 11.4 concerns only
the first separator. $\square$

**Theorem 11.7 (two universal whole-table charging principles fail).**
Consider the class of all Definition 3.1 threshold tables feasible at
$(n,W)$, with $n\ge6$, $3\le k\le n-2$ and original distinct
positive selected positions. For a fixed representative system, let
$E$ be any cell-disjoint collection of its fixed-history collisions
satisfying Theorem 7.1 with $\lambda=v=1$. Write $s(e,\omega)$
and $P(e,\omega)$ for their first separators and packs.

There is no dimension-independent finite constant $C$ for which,
for every table, every lawful representative system and every such
$E$, one can jointly choose allowed completions $(\omega_e)_{e\in E}$
so that

$$
\left|\{e\in E:s(e,\omega_e)=q\}\right|\le C
\quad\text{for every installed running state }q.
\tag{WTF.44}
$$

Also false is the principle with those same universal quantifiers
which permits joint completion choices and requires an injection
$e\mapsto q_e$ into $Q_B\setminus\operatorname{im}f$ with
$q_e\in P(e,\omega_e)$. It fails even when injectivity is dropped
and $E$ consists of only one collision.

Proof. Given $C$, choose an integer $M\ge2$ with $M-1>C$.
Theorem 11.3 gives a complete cap-feasible table, and Proposition
11.6 gives one lawful representative system. Take the $M-1$ pairs
$\{L_j,H_j\}$, $2\le j\le M$, for $E$. They are cell-disjoint
and satisfy all stipulated parameters by (WTF.41). For every joint
completion choice Theorem 11.4 gives $s(e,\omega_e)=J$ for all
$e$. Thus its multiplicity is $M-1>C$, contradicting (WTF.44).
The joint existential choice of completions cannot repair this failure.

For the external-pack principle keep that same table and representative
system but take $E=\{\{L_2,H_2\}\}$. By (WTF.43), no allowed
completion supplies even one state of its pack outside the image.
Hence the asserted assignment does not exist, before any question of
injectivity. These are counterexamples to principles quantified over
whole feasible tables and arbitrary fixed lawful representative
systems, with the actual incoming histories held fixed.

The first statement rules out bounded reuse of these first separators
as a universal replacement for injective charging. The second rules
out accepting an arbitrary representative system and subsequently
repairing its collisions solely with external states from these packs,
even after coordinating completions. Neither asserts a false numerical
inequality $m_B<G$: Theorem 11.3 instead gives $m_B>G$. Other installed
states and a new jointly chosen representative system are different
possible sources of compensation. In particular Proposition 11.5
shows that this very table has a favorable injective choice. $\square$

**Proposition 11.8 (scope, suppliers and the unchanged strict-subgrid
question).** The preceding obstruction concerns first separators of
fixed histories and external packs for arbitrary fixed representatives
over all cap-feasible whole tables. It does not refute a theorem
restricted to minimum or subgrid tables, favorable joint selection of
representatives, a count using other installed states, or a global
compensation or no-larger replacement theorem. The original question
for general $n\ge6$, $3\le k\le n-2$ remains whether

$$
\exists\, B:\quad
m_B<k(n-k+1),\qquad
q_B(\theta)\le n,\qquad L_B(\theta)\le W
\quad\text{for every }\theta\in\{0,1\}^n,
\tag{WTF.45}
$$

with correctness and termination on every input, or whether every
such table instead has $m_B\ge k(n-k+1)$. By Theorem 4.1 these
are the unchanged original full-fiber alternatives at
$H<k(n-k+1)+4+r$, $p\le n+1$, $\ell\le3+W$.
Neither alternative is resolved by Theorems 11.3–11.7.

Proof. The example is strictly above the grid, and PCA Theorem 26.1
already supplies a smaller table at both caps. It therefore cannot
witness (WTF.45) or obstruct a restriction to installed-state minima.
Proposition 11.5 supplies favorable representatives on this same
example. Theorem 11.7 excludes exactly its two displayed universal
witness-selection principles, not compensation by other vertices or
replacement of an entire table. These establish the stated logical
boundaries.

The reused mathematics is PE Theorem 5.1's paid mixed-private AND/OR
motif and inequalities, Theorem 7.1's certificate construction, and
Theorem 4.1's exact native transport. PCA Lemma 24.1 and the NBP/TMC
suppliers of §2 provide actual origins, all-address interpretation,
complete rows and the original reader. The further deduction is the
unbounded all-completion first-separator obstruction for the specified
cell-disjoint histories, its fixed-representative external-pack consumer
and the explicit favorable-choice contrast. The qualitative warning
in §9, elementary tree counts, positional uniqueness and generic
Boolean path facts are suppliers, rather than additional claims of
new general mathematics.

The primary comparison remains exactly Comparison 10.2. Wegener,
[Chapter 14 §4, printed pp. 423–425][WBP], proves synchronous
symmetric normalization for BP1; printed p. 424 restricts its graph-path
realization assertion to BP1. Sinha, [§2.1.3, printed p. 17][SINHA],
allows union cycles without semantic cycles and describes leveling
with $(l+1)s$ states. Neither supplies a cardinality-preserving BP1
replacement under the present paid-repeat hypotheses. These comparisons
support the restrictions stated here and do not establish worldwide
novelty of the specified obstruction.

Theorems 55.2, 59.1 and 63.1–66.1 of
[Native long-time phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md)
concern the stationary Q height law, supplied continuous wrapped phase
records, finite-sample Bayes risks or calibration recovery. Those
sources, observations and targets differ from $\mathcal U_*$,
fixed absolute native queries and literal complete entries here.
No map identifying their stochastic path resources with all installed
states and both original uniform caps is a premise above. Thus those
results do not replace either alternative in (WTF.45); no phase record,
conditioning, sensor or calibration service is imported into $B_M$.
Assumption 1.5's separate service and physical-price boundaries remain
in force throughout. $\square$

## 追加锚（本行以下为增补区）
