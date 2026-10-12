# Signed joint memory for complete original recuts

> This `generic-v1` volume studies one paid, actually acquired signed input. It is
> ordinary mathematical exposition; it makes no Lean, Blueprint, registry,
> digestion, physical-erasure or external-priority claim. The target is the
> complete original $Q$-row, including its exterior, reached holes and whole
> equality partition. The source is always one finite ordered tree, and the
> interpreted operation $\rho$ is never treated as a free unary constructor.

## 1. The acquired source and the service contract

**Definition 1.1 (native source algebra).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle s,t\rangle,
\qquad
\rho\alpha=\beta,
\quad
\rho\beta=\langle\beta,\alpha\rangle,
\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle .
\tag{SJM.1}
$$

The trees are nonempty, finite, free and ordered. Every occurrence is retained;
there is no sharing, associativity or commutativity quotient. Put
$T_j=\rho^j\alpha$. The atomic recurrence supplied by the native algebra is
$T_{j+2}=\langle T_{j+1},T_j\rangle$. For a finite address $p\in\{L,R\}^*$,
$r_u(p)$ is the four-valued reply
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$, with absence below a leaf.
The operation $\rho$ is interpreted by (SJM.1) and used only through finite
native transport; no free unary symbol or contracting metric is assumed.

We use the finite right-spine clock

$$
\kappa(\alpha)=0,\qquad \kappa(\beta)=1,\qquad
\kappa(\langle s,t\rangle)=2+\kappa(t).
\tag{SJM.2}
$$

Structural induction gives $\kappa(\rho u)=\kappa(u)+1$. Define

$$
F(u)=\langle\beta,\rho u\rangle .
\tag{SJM.3}
$$

Then $\kappa(Fu)=\kappa(u)+3$, so, for every finite $u$,

$$
 u\ne\rho u,\qquad u\ne Fu,\qquad \rho u\ne Fu.
\tag{SJM.4}
$$

The clock is used only as a finite-tree inequality witness; it is not a source
clock or an extra observation port.

**Definition 1.2 (complete signed input).** Fix finite prefix-free original cuts
$P,Q$, an attained complete old row $R_P$, a finite literal list $H_0$, and a
finite list $H_{\rm rel}$ of records
$e=(a,p,b,q,\bowtie)$ with $\bowtie\in\{=,\ne\}$. A literal requires
$r_{\rho^a u}(p)$ to equal its stated reply. A relation record means

$$
\operatorname{Rel}_e(u)\;:\Longleftrightarrow\;
 p\in\operatorname{Pos}(\rho^a u)\ \land\ q\in\operatorname{Pos}(\rho^b u)\ \land
 (\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q .
\tag{SJM.5}
$$

Both endpoints must be reached for either sign. The entire original-source fiber is

$$
D=\{u\in\mathcal T:R_P(u)=R_P,\ H_0(u),\
\bigwedge_{e\in H_{\rm rel}}\operatorname{Rel}_e(u)\}.
\tag{SJM.6}
$$

This retains every old equality class, every cross-class disequality (including
classes outside $Q$), all concrete exterior and all guards. It is not a selected
subfamily described by a later label.

**Assumption 1.3 (paid complete handoff).** The input in Definition 1.2 is the
output of one source-total paid producer on the same original root and register.
It traverses the finite source, acquires the endpoint descriptions at their
actual epochs, computes all signs, reaches a certified current epoch
$N\ge\max(\{0\}\cup\operatorname{epochs}(H_0,H_{\rm rel}))$, and then makes a
complete cut. Every accessible source-dependent field, including handles,
lengths, control positions, timing, archives and permissions, factors through
$(P,Q,R_P,H_0,H_{\rm rel},N)$ and any explicitly declared additional field.
No source-dependent selector is free advice. This is the paid acquisition
correspondence of [ARH, Proposition 2.1][ARH].

After the cut, a legal consumer is deterministic, effective and correct on every
$u\in D$. It may issue actual four-valued $\mathsf{Read}(p)$ calls at the current
register, real same-register forward $\mathsf{ApplyRho}$ calls and absorbing
$\mathsf{Halt}$. There is no reset, reroot, clone, equality oracle,
image-membership oracle, source label, clock port or old-version read. Local work,
address length, updates, preparation, installation, retention, memory and time
are separate resources. A uniform read bound counts every actual read, including
repetitions and absent replies.

**Definition 1.4 (the full target and inclusive prefixes).** The target is
$f(u)=R_Q(u)$, consisting of the reached original $Q$ addresses, the concrete
numbered-hole exterior and the complete equality partition of the whole reached
subtrees. For $h\ge0$, write

$$
 p_h(u)=(r_u(w))_{|w|\le h},
 \qquad u\equiv_h v\;:\Longleftrightarrow\;p_h(u)=p_h(v).
\tag{SJM.7}
$$

The absent reply is included in $p_h$. A source prefix is an attained finite
reply table, not an arbitrary word over four symbols.

## 2. The exact conditional alphabet

**Definition 2.1 (row strata and prefix multiplicity).** Assume first that
$A=f(D)$ is finite and nonempty. For $r\in A$ put
$D_r=\{u\in D:f(u)=r\}$. For an attained prefix $p$, set

$$
S_h(p)=\{r\in A:\exists u\in D_r\text{ with }p_h(u)=p\},
\qquad
m_h=\max_{p\ {\rm attained}}|S_h(p)| .
\tag{SJM.8}
$$

The sequence $m_h$ is nonincreasing. Let $I=(P,Q,R_P,H_0,H_{\rm rel},N)$.
An admissible extra field is a source-total effective map $E:\mathcal T\to C$,
actually computed from the same acquired finite source before the complete cut,
with finite nonempty conditional image $E(D)$. Its program and installed data
are common functions of $I$ and declared source-independent parameters. The
entire accessible initial state factors through $(I,E(u))$ and recovers these
fields; no source-dependent program, selector, length, timing or archive lies
outside them. Define $M(D,Q)$ to be the least $|E(D)|$ over such fields for
which one common effective consumer terminates correctly on every $u\in D$,
has a uniform finite number of post-entry reads, and returns $f(u)$.
Only complete conditional values are minimized. The acquisition, computation,
installation and complete cut must actually be supplied and paid.

**Theorem 2.2 (minimum complete field and static reduction).** Under
Assumption 1.3, if $A$ is finite and nonempty, then

$$
\boxed{
M(D,Q)=\min_{h\ge0}m_h
=\max_{\xi}\bigl|\{r\in A:\xi\in\overline{D_r}\}\bigr| .}
\tag{SJM.9}
$$

The closure is in the prefix topology of finite or infinite full ordered trees
over $\alpha,\beta,\langle\ ,\ \rangle$, with no descendants below a leaf.
The minimum is attained at a finite $h$. The same value holds when the consumer is
allowed every legal adaptive serial $\mathsf{ApplyRho}$ strategy, and when it is
restricted to static reads at the supplied epoch. This equality concerns only the
number of complete conditional field values; it does not identify an optimal raw
call, address-length or update price.

*Proof.* Let a proposed field have $m$ attained values and let its consumer use
at most $K$ reads. Fix one field value $e$. Between two replies, the consumer's
computation and update schedule are source-independent and terminate on every
source reaching that segment. Unrolling the reachable four-valued reply histories
therefore gives a finite tree. Across the $m$ values, only finitely many physical
addresses are submitted; let $h$ be the largest address length, taking $h=0$
if no address is submitted.

The original-address locality clause (SLH.74.7), including born and absent
positions, says that a reply at any declared epoch from an address of length at
most $h$ is determined by the inclusive original depth-$h$ table. Thus two
sources with the same $E$ value and the same $p_h$ produce the same adaptive
serial run and the same output. If one attained prefix $p$ meets $k$ different
rows, selecting one source from each of those strata forces $k$ different field
values. Hence $m\ge m_h\ge\min_jm_j$.

The argument did not assume the field was constant on rows: arbitrary effective
encodings are covered. The common-state premise is applied separately to each
nonempty $D_e=\{u\in D:E(u)=e\}$. For the same given effective $E$, the
inherited existence bridge is precisely

$$
\begin{aligned}
&\text{uniform finite-read serial service using }(I,E)\\
\Longleftrightarrow\;&\text{uniform finite-read static service using }(I,E)\\
\Longleftrightarrow\;&\exists h\ \forall e\in E(D),\quad
 \operatorname{PrefDet}(D_e,Q,h).
\end{aligned}
\tag{SJM.10}
$$

Here $\operatorname{PrefDet}(X,Q,h)$ means that $p_h$ determines the full
$Q$-row on $X$. The serial-to-prefix proof of [ARH, (ARH.2.3)][ARH] uses only
the common initial state and locality, so it applies on each $D_e$; take the
maximum depth over the finitely many values. Conversely, given $e,h$ and the
actually decoded prefix, enumerate finite sources until finding one in $D$
with that prefix and $E(u)=e$. Membership of $D$ is decidable on a concrete
source and the source-total encoder terminates, so each candidate test
terminates. The actual source witnesses eventual success; $\operatorname{PrefDet}$
makes the candidate's full row the correct output. The static prefix menu has
a common finite read bound. No effective extraction of $h$ from arbitrary
consumer code is claimed. In particular (SJM.10) does not assert unassisted
prefix determination on the unconditioned $D$.

For the converse bound, take a supplied source-independent $h$. Here is the
exact finite table compilation. First [NPL, Theorem 5.3][NPL], on the entire
input (SJM.6) and cut $Q$, returns $A$, including each concrete exterior,
reached set and full partition, and an original realizing source for each row.
Lemma 5.2 there supplies the guarded native cells; Theorem 5.3 additionally
decides their mask images and every complete partition, so it supplies the
row list that the rank construction needs. Order that list canonically by
finite serialization. For each four-valued table $p$ on the finitely many
words $|w|\le h$ and each $r\in A$, decide

$$
\exists u\in\mathcal T,\quad
u\in D\ \land\ R_Q(u)=r\ \land\
\bigwedge_{|w|\le h} r_u(w)=p(w)
\tag{SJM.35}
$$

using [NSF, Lemma 5.1 and Theorem 5.2][NSF]. These are fixed-coordinate and
fixed-complete-row tests on one whole source; every old class disequality,
off-task constraint, literal and signed reach guard remains in $D$.
A YES answer supplies an actual finite original witness. The YES labels are
exactly $S_h(p)$; discard tables with no YES label. This both removes
unrealizable reply tables and retains every actual prefix. There are finitely
many tables and rows and each query terminates. The resulting installed table
depends only on $I,h$, never on a hidden choice of source.
During the same paid pre-cut acquisition, compute the actual full row and retain

$$
E_h(u)=\text{the zero-based rank of }f(u)\text{ in the canonical list }S_h(p_h(u)).
\tag{SJM.11}
$$

The producer obtains the needed original descriptions during the paid traversal,
computes $f(u)$ and $p_h(u)$, and evaluates this rank before cutting all other
source-bearing state. On concrete sources outside $D$ it uses default value
$0$; membership is decidable, and $m_h\ge1$, so this extends $E_h$ to a
source-total effective map without adding a conditional value. All successful
accessible fields factor through $(I,E_h)$; the paid descriptions do not remain
available after the cut. Neither the program nor $h$ is selected from the
actual source outside the charged field. At the actual current epoch $N$,
recover all replies in $p_h(u)$ by the supplied current-register decoder
[SLH, Theorem 2.2][SLH]. At most $2(2^{h+1}-1)$ physical reads suffice, with submitted address
length at most $h+\lceil N/2\rceil$. The consumer then looks up the rank and
returns the complete row. A prefix attaining $m_h$ realizes every rank below
$m_h$, so the conditional field has exactly $m_h$ values. This proves the first
equality in the other direction and gives a static consumer, hence a legal serial
one.

For the closure identity, if $k$ row strata share a completion point $\xi$, each
finite depth of $\xi$ is met by all $k$ strata, so $m_h\ge k$ for every $h$. In
the reverse direction, suppose $m_h\ge k$ for all $h$. Since $A$ is finite,
one $k$-element set of row labels occurs for arbitrarily large $h$, hence at
every depth by restriction. Its tree of common finite reply prefixes is closed
under restriction, finitely branching, and has a node at every depth. König's lemma gives a compatible finite or infinite completion
meeting all those strata, so its closure multiplicity is at least $k$.
Finally, $m_h$ is a nonincreasing sequence of integers between $1$ and $|A|$;
it stabilizes at a finite depth. $\square$

**Proposition 2.3 (effective finite depths and the optimizer boundary).** For each
fixed $h$, the exact finite list of $S_h(p)$ and the value $m_h$ are decidable.
Consequently $m_h$ gives a computable decreasing approximation to $M(D,Q)$, and
$M\le k$ is semidecidable by searching for an $h$ with $m_h\le k$. For every
fixed attained finite-image input, some finite minimizing $h$ exists and (SJM.11)
gives an effective optimal installation once that $h$ is supplied. No uniform
terminating procedure for finding a minimizing $h$ on arbitrary signed input is
claimed.

*Proof.* Apply the exact full-row-list and one-source compiler (SJM.35).
It returns every $S_h(p)$, its realizing original sources and the maximum
cardinality $m_h$. Refining a prefix can only remove labels, which proves
monotonicity. A nonempty finite image bounds this decreasing integer sequence
between $1$ and $|A|$, so its minimum is attained. The final sentence is a
quantifier distinction: existence of a finite minimizer supplies an effective construction
parameterized by that witness, but does not provide a terminating search that
knows no later depth lowers the value. $\square$

**Corollary 2.4 (edge cases).** If $A$ is a singleton, $M=1$ and a constant field
supports zero reads; this is zero additional information in the usual coding
sense. With zero post-entry reads and finite $A$, exactly $|A|$ complete field
values are necessary and sufficient. If $A$ is infinite, no finite complete field
supports any uniform finite-read exact service. The empty fiber is outside the
attained-entry promise.

*Proof.* The singleton and zero-read claims follow by counting outputs. For an
infinite $A$, a field of size $m$ and a $K$-read four-reply tree have at most
$m4^K$ terminal outputs, contradicting the infinitely many distinct rows. $\square$

The closure formula in (SJM.9) is deliberately restricted to finite $A$. For
example, with $Q=\varnothing$ and all finite sources admitted, each source is a
singleton row stratum and the target image is infinite; the finite-image closure
identity must not be applied to that case.

## 3. The remaining all-depth joint obligation

**Definition 3.1 (simultaneous contact predicate).** For distinct rows
$r_1,\ldots,r_k\in A$, write

$$
J_{r_1,\ldots,r_k}(h)
\;:\Longleftrightarrow\;
\exists u_i\in D_{r_i}\ (u_1\equiv_h\cdots\equiv_h u_k).
\tag{SJM.12}
$$

The all-depth assertion is $\forall h\,J_{r_1,\ldots,r_k}(h)$ with fresh finite
witnesses allowed at each depth. It does not require an infinite source satisfying
the signed predicates.

**Theorem 3.2 (fixed sets, multiplicity bounds and minimization).** Assume
$A$ is finite and nonempty. For a nonempty subset $B\subseteq A$, use $J_B(h)$
for (SJM.12) with exactly those labels. Each fixed $J_B(h)$ is decidable, and

$$
\begin{aligned}
m_h<k
&\Longleftrightarrow
 \forall B\subseteq A,\ |B|=k\Longrightarrow\neg J_B(h),\\
M(D,Q)<k
&\Longleftrightarrow
 \forall B\subseteq A,\ |B|=k\Longrightarrow
       \exists H_B\ \neg J_B(H_B),\\
M(D,Q)
&=\max\{|B|:\varnothing\ne B\subseteq A,\ \forall h\ J_B(h)\}.
\end{aligned}
\tag{SJM.36}
$$

The first two lines hold for $1\le k\le |A|+1$, with a vacuous family when
$k>|A|$. A fixed $k$-set's exclusion says only that this set does not jointly
occur at that depth. Excluding **every** $k$-set gives $m_h<k$.
Full unassisted determination is the special case $k=2$: it is equivalent to
some depth excluding every distinct row pair, and hence to $M=1$.

*Proof.* For fixed $B,h$, apply NSF Lemma 5.1 and Theorem 5.2 to $|B|$
independent whole-source variables. Each copy satisfies all of (SJM.6) and its
specified complete target row; impose identical four-valued replies at every
word $|w|\le h$. All epochs, words, cuts and row constants are finite supplied
values. YES produces each original finite source, including all signed guards
and off-task constraints. The query is exactly $J_B(h)$ in both directions.

At depth $h$, $J_B(h)$ holds exactly when some attained prefix has
$B\subseteq S_h(p)$, proving the first line. Each $J_B$ is downward closed in
$h$. If all $k$-sets have failed depths, take their finite maximum (zero for
an empty family); every such set still fails there, so $m_h<k$ and $M<k$.
Conversely, a depth with $m_h<k$ excludes each $k$-set. This proves the second
line without confusing multiplicity with uniqueness.

A persistent $k$-set gives $m_h\ge k$ for all $h$, hence $M\ge k$.
Conversely, if $M\ge k$, at every $h$ some $k$-set has contact. Finitely many
$k$-sets are available, so one occurs at arbitrarily large depths; downward
closure makes that same set persistent at every depth. At least one singleton
is persistent, and no set has size larger than $|A|$. This proves the maximum
formula and also covers $k=1$, where contact of each attained singleton is
always true. Taking $k=2$ gives the stated unassisted determination criterion.

Thus a minimizing depth $h_*$ is certified by an upper bound $m_{h_*}=m$
and a persistent $m$-set, not by exclusion of one set or by a temporary plateau.
If a terminating all-depth chooser for every fixed $B$ were supplied, finitely
many calls would find the largest persistent size $m$ and exclusion depths for
all $(m+1)$-sets. Their maximum yields $m_h\le m$; the persistent set gives
the matching lower bound. When $m=|A|$, there are no larger sets and $h=0$
suffices. The rank encoder then follows from Theorem 2.2.

No such complete all-depth chooser or general minimizing-depth synthesis is
supplied here. Fixed-depth decisions and a supplied productive mechanism do
not prove that arbitrary contacts have a finitely recognizable persistent
case. Deciding a fixed set's persistence is a sufficient route to the global
optimizer, not a claim that every optimizer must decide every fixed set.
The unsupplied all-depth/finite-realization boundary is consistent with
[NPL, §10][NPL] and [ARH, Definition 9.1][ARH]; neither reference proves the
multi-label synthesis now required. No undecidability claim follows. $\square$

An observed plateau of the computable values $m_h$, finitely many tests, or a
valid supplied guarded certificate at a prescribed budget does not prove that
no later depth lowers the value. The complete-handoff premise and the finite
realization of every positive witness remain required at every finite stage.

## 4. Two actually acquired native fibers

The next construction is a native simultaneous-contact separation. Both inputs
use the same one-hole root row, target cut and root-based register interface,
and one common paid producer implementation parameterized by public coordinate
lists. The literal and positive-relation coordinate lists differ as displayed;
the negative-relation lists are identical. In each run every record and later
read concerns that run's same actual original source, root and register.
All witnesses below are finite actual sources; no negative is tested only at a
limiting completion.

**Definition 4.1 (the three-value fiber).** Let $P=\{\varepsilon\}$ with its
complete one-hole old row and let

$$
Q=\{L,RL,RRL,RRR\}.
\tag{SJM.13}
$$

Use the epoch-zero literals

$$
(0,\varepsilon,\mathsf{branch}),\quad
(0,R,\mathsf{branch}),\quad
(0,RR,\mathsf{branch}),\quad
(0,RRR,\mathsf{branch}),\quad
(0,RRRL,\beta),
\tag{SJM.14}
$$

and the positive records

$$
(1,RL,0,RRL,=),\qquad (0,RRL,0,RRRR,=).
\tag{SJM.15}
$$

Add the reached negative records

$$
(0,RL,0,RRL,\ne),\qquad
(0,RL,0,RRR,\ne),\qquad
(0,RRL,0,RRR,\ne).
\tag{SJM.16}
$$

Take any common certified final epoch $N\ge1$. Define

$$
U(y,z)=\langle z,\langle y,\langle\rho y,Fy\rangle\rangle\rangle .
\tag{SJM.17}
$$

**Proposition 4.2 (exact source fiber and four complete rows).** The entire
successful fiber of (SJM.14)–(SJM.16) is

$$
D_3=\{U(y,z):y,z\in\mathcal T\}.
\tag{SJM.18}
$$

Every source reaches all four $Q$ holes, with the same exterior
$\langle\square_1,\langle\square_2,\langle\square_3,\square_4\rangle\rangle\rangle$.
Its complete row is exactly one of

$$
\begin{array}{c|c}
 r_0&z=y\ne\rho y,Fy\\
 r_1&z=\rho y\ne y,Fy\\
 r_2&z=Fy\ne y,\rho y\\
 r_3&z,y,\rho y,Fy\text{ are pairwise distinct}.
\end{array}
\tag{SJM.19}
$$

All four rows are attained.

*Proof.* The literals force every displayed pair root and the explicit $\beta$
leaf, so every successful source has the form
$\langle z,\langle y,\langle v,\langle\beta,w\rangle\rangle\rangle\rangle$.
The first record in (SJM.15) compares the current epoch-one subtree at $RL$,
which is $\rho y$, with the original subtree $v$ at $RRL$; hence $v=\rho y$.
The second record gives $w=v$. Thus the source is exactly (SJM.17), and all
endpoints are reached by (SJM.14). Conversely every $U(y,z)$ satisfies the
literals and both equalities. The three inequalities follow from (SJM.4), so
both directions give the entire fiber, including all guards.

The four target holes contain $z,y,\rho y,Fy$. The three reference values
$y,\rho y,Fy$ are pairwise unequal by (SJM.4). Therefore the arbitrary $z$
can equal at most one reference value. It equals one of them or differs from
all three, giving exactly the four complete partitions (SJM.19); no inequality
between $z$ and a reference is assumed before selecting that case. The choices
$z=y$, $z=\rho y$, $z=Fy$ attain $r_0,r_1,r_2$, and $z=\rho^2y$ attains
$r_3$, since $\kappa(\rho^2y)=\kappa(y)+2$ differs from the offsets
$0,1,3$. The exterior and reached set are fixed, so these are the complete rows,
not merely labels. $\square$

**Definition 4.3 (the four-value fiber).** Keep $P,Q$ and the same root row, and
use literals

$$
\begin{gathered}
(0,\varepsilon,\mathsf{branch}),\ (0,R,\mathsf{branch}),\ (0,RR,\mathsf{branch}),\
(0,RRL,\mathsf{branch}),\ (0,RRR,\mathsf{branch}),\
(0,RRLL,\beta),\ (0,RRRL,\beta),
\end{gathered}
\tag{SJM.20}
$$

with positive records

$$
(1,RL,0,RRLR,=),\qquad (1,RRL,0,RRRR,=),
\tag{SJM.21}
$$

and negatives

$$
(0,RL,0,RRL,\ne),\qquad (0,RL,0,RRR,\ne),\qquad
(0,RRL,0,RRR,\ne).
\tag{SJM.22}
$$

Again use the common final epoch $N\ge1$. Put

$$
V(y,z)=\langle z,\langle y,\langle Fy,F^2y\rangle\rangle\rangle .
\tag{SJM.23}
$$

**Proposition 4.4 (the second exact fiber and the same four rows).** The entire
successful fiber of (SJM.20)–(SJM.22) is

$$
D_4=\{V(y,z):y,z\in\mathcal T\}.
\tag{SJM.24}
$$

Its four complete rows are the same $r_0,r_1,r_2,r_3$ in (SJM.19), with
$\rho y,Fy$ replaced by $Fy,F^2y$ in the hole values and the same equality
partition names.

*Proof.* The literals force the outer skeleton and the two left $\beta$ leaves.
At epoch one the subtree at $RL$ is $\rho y$, so the first equality forces the
right child of $Fy$ to be $\rho y$. At epoch one the subtree at $RRL$ is
$\rho(Fy)$, so the second equality forces the right child of $F^2y$ to be
$\rho(Fy)$. Thus the source is (SJM.23). Conversely (SJM.23) satisfies every
literal, equality and reach guard. The clock gives offsets $0,3,6$ for
$y,Fy,F^2y$, so all three negative records hold. The target partition analysis is
identical, and $z=F^iy$ for $i=0,1,2,3$ attains all four rows because the
offsets $0,3,6,9$ are distinct. $\square$

**Proposition 4.5 (same pair contacts, but minima three and four).** For
$i\ne j$ and $h\ge0$, let $J^{(3)}_{ij}(h)$ and $J^{(4)}_{ij}(h)$ be the
pair-contact predicates (SJM.12) for $D_3$ and $D_4$. Then

$$
J^{(3)}_{ij}(h)=J^{(4)}_{ij}(h)=\mathsf{true}
\qquad(i\ne j,\ h\ge0),
\tag{SJM.25}
$$

but

$$
M(D_3,Q)=3,\qquad M(D_4,Q)=4.
\tag{SJM.26}
$$

*Proof.* First establish the finite-prefix claims used by the witnesses.
For $n\ge2h+2$, recurrence (SJM.1) makes every reply of $T_n$ through depth
$h$ a branch: along a path of length at most $h$, its index falls by at most
$2h$, and every remaining index is at least $2$. Thus $T_n,T_{n+1},T_{n+2}$
agree through any prescribed depth when $n$ is large. The three sources

$$
U(T_n,T_n),\quad U(T_n,T_{n+1}),\quad U(T_n,T_{n+2})
\tag{SJM.27}
$$

have rows $r_0,r_1,r_3$ respectively, and all retained signs hold by the
clock. This gives the three contacts among $r_0,r_1,r_3$ in $D_3$.

For the remaining contacts use $F(t)=\langle\beta,\rho t\rangle$ and
$B(t)=\langle\alpha,t\rangle$. Locality (SLH.74.7) at epoch one gives
$u\equiv_h v\Rightarrow\rho u\equiv_h\rho v$. Hence either $F$ or $B$
increases agreement depth by one, since it inserts a common branch and left
leaf above its argument or its iterate. For arbitrary finite $u,v$, $F^n(u)$
and $F^n(v)$ agree through depth $n-1$: the case $n=1$ is the common branch
root, and induction proves the claim. The same statement holds for $B$.
In particular $F^n\beta$ and $F^{n+j}\beta$ agree through depth $n-1$
for every $j\ge0$, and likewise for $B$. These stabilized compatible
prefixes define completions $K,J$ with $F(K)=K$ and $B(J)=J$.
Here $\rho$ on a completion means only its continuous prefix extension
supplied by locality; no completion is asserted to satisfy a signed input.
Since $J=\langle\alpha,J\rangle$,
$\rho J=\langle\beta,\rho J\rangle=FJ$.
The triples

$$
\bigl(U(F^n\beta,F^n\beta),\ U(F^n\beta,F^{n+1}\beta),\
      U(F^n\beta,F^{n+2}\beta)\bigr)
\tag{SJM.28}
$$

have rows $r_0,r_2,r_3$ and agree through every prescribed finite depth for
large $n$. Likewise

$$
U(B^n\beta,\rho B^n\beta),\quad
U(B^n\beta,\rho B^{n+1}\beta),\quad
U(B^n\beta,\rho B^{n+2}\beta)
\tag{SJM.29}
$$

have rows $r_1,r_2,r_3$: the offsets $1,3,5$ are distinct, while
$\rho J=FJ$ makes their three $z$-components share the same prefix limit.
Equations (SJM.27)–(SJM.29) cover all six row pairs. They are finite sources and
therefore verify every negative at the finite stage; no sign is transferred to a
limit.

For $D_3$, no depth-three prefix can meet $r_0,r_1,r_2$ simultaneously. In an
$r_2$ source, $z=Fy$ has a branch root with left reply $\beta$. A common depth-
three prefix would therefore make the $r_0$ source satisfy that $y=z$ is a branch
whose left reply is $\beta$. In the $r_1$ source, $z=\rho y$ has the same branch
root and left reply. Given the common branch root of $y$, the native definition of
$\rho$ then forces its left child to be $\alpha$ (if $y=\langle a,b\rangle$,
its left child after applying $\rho$ is $\rho a$, and $\rho a=\beta$ implies $a=\alpha$).
The $r_0$ source forces that left child to be $\beta$, a contradiction at the
address $RLL$. Hence $m_3\le3$. The displayed atomic triple, with $n$ beyond any given
$h$, gives $m_h\ge3$ for every $h$, so $\min_hm_h=3$.

For $D_4$, let $y_n=F^n(\beta)$. For each $i=0,1,2,3$, the source
$V(y_n,F^i y_n)$ has row $r_i$. All four components converge to the same
prefix completion $V(K,K)$, and every finite source satisfies (SJM.22). Thus
$m_h\ge4$ for every $h$. Since there are only four rows, $m_h=4$ for all $h$,
so $\min_hm_h=4$. Theorem 2.2 now proves (SJM.26).

The public lists (SJM.14)–(SJM.16) and (SJM.20)–(SJM.22) are two parameter
instances of the same paid traversal and comparison procedure of ARH
Proposition 2.1, at a common final epoch $N$. For either list the producer
computes both signs, with invalid reached-endpoint outcomes kept separate;
conditioning on the stated successful output gives exactly the fiber proved
above. Every record on each witness is an actual reached comparison on that
witness's same source and register. No arbitrary graph or completion substitutes
for either original-source direction. The off-diagonal Boolean contact
matrix is the complete graph $K_4$ in both cases, while the simultaneous contact
number, and hence the minimum field, differs. $\square$

**Proposition 4.6 (attained encoders and current-epoch consumers).** The value
three in $D_3$ is attained by a three-value complete field, and the value four in
$D_4$ by a four-value complete field.

*Proof.* For $D_3$ use $h=3$ in (SJM.11). During the paid pre-cut traversal
of ARH Proposition 2.1, the common producer computes the full $Q$-row and
original depth-three table from the actually acquired descriptions, then stores
the rank in the canonical $S_3(p_3(u))$ list. Its successful complete cut
retains only the declared input and this code; the traversal descriptions,
lengths and control distinctions are no longer accessible. Proposition 4.5 shows
that some attained depth-three prefix has exactly three rows, so all three ranks
occur. The consumer reconstructs the inclusive original depth-three table at the
actual register epoch $N$ using [SLH, Theorem 2.2][SLH] and returns the whole
exterior and partition from the rank. This is a real current-register consumer,
with at most $2(2^4-1)=30$ reads and no old-version access.

For $D_4$, store the rank of the complete row in the fixed ordered list
$(r_0,r_1,r_2,r_3)$. It has four attained values and the consumer returns that
row with zero post-entry reads. The lower bounds in Proposition 4.5 apply to
all complete encodings and all legal adaptive serial competitors, so these are
exact minima rather than properties of a chosen label field. $\square$

## 5. A real read that lowers the minimum to one

**Proposition 5.1 (the acquired $3\to1$ continuation).** In the three-value
fiber $D_3$, enter at the actual epoch $N=1$ and make the legal physical read

$$
\mathsf{Read}(RL)=\beta .
\tag{SJM.32}
$$

This outcome is attained. First consider entry with only the declared input,
without an extra code. A paid complete successor handoff retaining precisely
that input and the new literal $(1,RL,\beta)$, with common ready control and
no other source-bearing state, has source fiber

$$
D'_3=\{U(\alpha,z):z\in\mathcal T\},
\tag{SJM.33}
$$

its complete original $Q$-row image is still exactly
${r_0,r_1,r_2,r_3\}$, and

$$
M(D'_3,Q)=1.
\tag{SJM.34}
$$

*Proof.* At epoch one the subtree at $RL$ is $\rho y$. From (SJM.1), the root
reply of $\rho y$ is $\beta$ exactly when $y=\alpha$; if $y=\beta$ or a pair,
that root is a branch. Thus the read has the exact source-fiber refinement
(SJM.33), with both directions. It is attained, for example, by any
$U(\alpha,z)$.

For $y=\alpha$, the three fixed target templates are

$$
\alpha,\qquad \rho\alpha=\beta,\qquad F\alpha=\langle\beta,\beta\rangle.
\tag{SJM.30}
$$

Choosing $z$ equal to these three values gives $r_0,r_1,r_2$, while
$z=\rho^2\alpha=\langle\beta,\alpha\rangle$ gives $r_3$. Hence the full
four-row image is preserved. The **whole original source** table $p_2$ contains
$L,LL,LR$, namely the root and depth-one child replies relative to $z$.
A leaf reply at $L$ identifies exactly $z=\alpha$ or $z=\beta$. If $L$ is a
branch, replies $\beta$ at both $LL,LR$ identify exactly
$z=\langle\beta,\beta\rangle$: leaves have no hidden descendants in the
native algebra. Every other pattern puts $z$ in $r_3$. These three replies
therefore determine the complete row on $D'_3$, whose other hole values and
exterior are fixed. Thus the root-based $m_2$ equals $1$ and Theorem 2.2 gives
(SJM.34).

At the same actual epoch one, apply the SLH Theorem 2.2 decoder to all seven
original words $|w|\le2$. This is at most $2(2^3-1)=14$ **further** physical
reads, each of length at most $2+\lceil1/2\rceil=3$, with no updates; together
with (SJM.32) it gives at most $15$ reads. The mathematical original replies
are inferred from those current-register replies, not accessed at a fictional
old version. The decoder then returns the complete exterior and partition.
No relative depth-two $z$ table (which would reach original depth three) is
used in this bound.

If entry already retains the old three-value field $E_3$ from Proposition 4.6,
the actual successor fiber retaining its value $e$ is
$D'_3\cap\{u:E_3(u)=e\}$, not the unconditioned $D'_3$. The old rank and its
old table still decode correctly on this refinement; no new preparation is
needed merely to keep using them. A complete successor cut may discard $e$
and any code-dependent control state and install a constant field. The resulting
state has exactly fiber $D'_3$, and the displayed decoder is sufficient there.
This replacement uses the actually acquired literal and a common fixed row
table; it needs paid local preparation, installation and cut, but no fresh
full-source traversal. A constant code is not a reinterpretation of the old
rank. With four rows still attained, zero-read recovery would instead require
four complete field values. $\square$

**Proposition 5.2 (known updates and refined code fibers).** After any known
finite sequence of forward updates, the original source $u$, the original target
$R_Q(u)$ and every acquired code value remain unchanged. The same code and its
original-prefix decoder remain valid at the new certified epoch, with the
corresponding current-register address transport. A further read
$\mathsf{Read}(p)=c$ at epoch $M$ refines the state to

$$
D'=D\cap\{u:r_{\rho^M u}(p)=c\},
\qquad
D'_e=D_e\cap\{u:r_{\rho^M u}(p)=c\}
\tag{SJM.31}
$$

for every old code value $e$, where $D_e=\{u\in D:E(u)=e\}$.
The physical reply must be actually attained, so $D'\ne\varnothing$; only
nonempty $D'_e$ are service entry fibers. In particular,
$M(D',Q)\le M(D,Q)$ for such a refinement whenever $f(D)$ is finite.

*Proof.* A known update changes only the physical register from $\rho^M u$ to
$\rho^{M+k}u$; it does not change the original source or the declared target.
[SLH, Theorem 2.2][SLH] converts each needed original prefix to reads at the
new actual epoch, so no old-version read or reset is inserted. If a decoder was
interrupted by an update, its bounded query list is restarted at the new
certified epoch; replies from different epochs are not spliced. The decoder's
stated bound applies after the last update; all interrupted and restarted reads
are additional actual calls and remain charged.

The new reply restricts every code fiber as shown in (SJM.31). At each depth
$S'_h(p)\subseteq S_h(p)$ for every prefix attained in $D'$, hence
$m'_h\le m_h$. At an old minimizing depth $h_*$ this gives
$M(D',Q)\le m'_{h_*}\le m_{h_*}=M(D,Q)$. Both images are nonempty and finite
because the reply is attained and $f(D')\subseteq f(D)$.
The same old code and decoder already give a correct bounded service on each
nonempty refined code fiber. If code-dependent path/control state remains
accessible, it must still factor through the retained input, code and recorded
replies. Using only $D'$ while forgetting $e$ describes a coarser state than
the actual handoff retaining $e$.

The inequality compares minima over newly admissible encoders; restriction
alone does not compute or acquire a new optimal code. Such a replacement
requires a justified source-total effective encoder, evaluated from actually
acquired data or further paid acquisition, together with paid preparation,
installation and a complete successor cut. Known updates alone need no new
code computation when the target remains the original $R_Q(u)$. Changing $Q$
changes the target and requires a new sufficiency argument. $\square$

## 6. Source correspondence, literature and boundaries

**Theorem 6.1 (resource and truth boundary).** The results above establish a
semantic minimum for complete conditional field cardinality and its actual native
attainment on the stated inputs. They do not establish a global stopping solver,
physical spacetime recovery, an optimal raw-read Pareto point, or completion of
the broader relation/space/time/boundary/memory programme.

*Proof.* The lower bound in Theorem 2.2 uses only the existing actual
prefix/locality and complete-handoff suppliers, and quantifies over every legal
serial competitor. The upper bound uses the same source description and current
register, with finite local enumeration. Propositions 4.2–4.6 and 5.1 use
finite sources and finite signed guards in both directions. Theorem 3.2
separates fixed-set exclusion, all-set multiplicity bounds and the global
optimizer. The latter still needs a certified minimizing depth and matching
all-depth lower evidence; a complete fixed-set chooser with source-faithful
witnesses would suffice but is not supplied. No statement here supplies that
stopping or realization mechanism.

The conditional alphabet charge is $|E(D)|$, not the size of $I$, installed
row/prefix tables, transient acquired descriptions, physical words or total
memory. All of these are separate paid resources. The rank table is finite
for each supplied $I,h$ but no uniform installation, local computation or
pre-cut acquisition bound across inputs is asserted. Current-prefix acquisition
uses the stated physical read and address-length upper bounds and no post-entry
updates; allowing real updates in the lower bound does not establish equal
minimum raw-call or update costs. Sourcewise finite traversal does not imply
uniform finite acquisition or physical time. The remaining claims are therefore
outside the proved scope. $\square$

**文献与来源表态。**

| 来源 | 精确转移与边界 |
| --- | --- |
| [ARH, §§1–3, (ARH.2.3)](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md) | `repo-derived`: complete signed source fiber, paid same-root producer, endpoint guards, current register and static/serial prefix bridge. It does not supply a uniform optimizer for arbitrary signed input. |
| [SLH, §§2, 59–75](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) | `repo-derived`: actual original-address locality and current-epoch decoding, including born and absent positions. It does not turn a finite test sequence into an all-depth stopping certificate. |
| [NPL, Lemma 5.2, Theorem 5.3 and §§6, 10](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md) | `repo-derived`: Lemma 5.2 provides complete guarded source cells; Theorem 5.3 decides finite/infinite complete-row image and returns the exact finite row list with original witnesses. Combined with NSF in (SJM.35), this compiles every supplied-depth rank table. It does not compute a global minimizing depth. |
| [NSF, Lemma 5.1 and Theorem 5.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md) | `repo-derived`: fixed-coordinate Boolean whole-source queries with supplied epochs, full row tests, all old constraints and signed endpoint guards. Positive answers reconstruct all original finite source copies. It does not decide the all-depth quantifier. |
| [NIC, Proposition 5.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md) | `repo-derived`: mixed interpreted-$\rho$ navigation and finite-depth signed feasibility. Its finite image cover is not a uniform synthesis theorem for arbitrary signed contacts. |
| [RDR, Theorem 6.2](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_ROW_DEPTH_RECOVERY.md) | `repo-derived overlap`: conditional rank coding for retained-row intrinsic depth. The present target is a signed full original recut and its native joint examples. |
| [SPC, §§2–5](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md) | `repo-derived`: finite productive signed witnesses and the discipline that every negative is checked on actual finite approximants. Supplied certificates are sufficient evidence, not complete stopping decisions. |
| `D5/S0/History/Coding/MinimumRollbackAlphabet.minimum_rollback_alphabet` | Exact finite process-fiber lower bound and fiberwise attaining labels. At fixed $h$ take $X_h=\{(p,r):r\in S_h(p)\}$, $Y$ the finite set of attained prefixes, $U(p,r)=p$ and $L(p,r)=r$; the largest process fiber is exactly $m_h$. ARH/SLH supply acquisition and current-register decoding. |
| Charpenay–Le Treust–Roumy, *Optimal Zero-Error Coding for Computing under Pairwise Shared Side Information*, Definition III.1 and the colouring equivalence in the proof of Theorem III.4, [arXiv:2211.03649](https://arxiv.org/abs/2211.03649) | `literature-attested`: at fixed $h$, use finite support $X_h=\{(p,r):r\in S_h(p)\}$, decoder side information $Y=p$, $g(Y)=Y$, encoder observation $X=(p,r)$ and target $r$; any positive distribution on this support gives disjoint prefix cliques of sizes $|S_h(p)|$. Proper colouring is exactly distinct labels within each prefix, and ranks attain $m_h$. Theorem III.4's asymptotic rate is not used. No stochastic acquisition or free physical side information transfers; ARH/SLH separately pay for and realize $p$. |
| Barguñó–Creus–Godoy–Jacquemard–Vacher, *Decidable Classes of Tree Automata Mixing Local and Global Constraints Modulo Flat Theories*, Theorem 5.22 and Corollaries 5.23–5.24, [arXiv:1302.6960](https://arxiv.org/abs/1302.6960) | `literature-attested`: emptiness for their constrained-tree-automaton classes. No faithful translation of arbitrary interpreted mixed-epoch $\rho$ histories or the unbounded joint-prefix obligation is assumed. |
| Milius–Moss, *The Category Theoretic Solution of Recursive Program Schemes*, §7.3 and Theorem 7.15, [arXiv:0904.2385v2](https://arxiv.org/abs/0904.2385v2) | `literature-attested`: interpreted guarded solutions as unique fixed points in the stated nonempty complete metric/contracting-functor setting. This is background only: Proposition 4.5 directly proves its needed prefix stabilization. No metric completeness of finite native sources, signed preservation on a limit, or completeness of finite productive descriptions transfers. |
| PR15621 at `0487ddfee131db56e40b654fad5a69689948e3c7` and PR15653 at `c0f820f0b4800326b5c9d06b23f11ce925b404fb` | Published overlap only: supplied-coordinate closure and guarded-description equality. They are not premises for arbitrary stopping or universal certificate completeness. |
| Retained literal root-depth manuscript, merged at `3508d303746985c18ca446a13c92b5c22f9df10d` | Static root target and specified normal-code continuation. It is distinct from this signed mixed-epoch full-row target. |

The canonical merged mathematical supplier pin for this volume is
`21dc7376d6bf6518ffd95621637dd6bb1ee8764d`. No external literature or repository
source cited here is being promoted to a kernel-certified premise.

**开放问题 6.2 (terminating signed joint synthesis).** For an arbitrary
attained input (SJM.6), first use NPL Theorem 5.3 to decide its entire full-row
image. An infinite answer excludes all finite complete fields by Corollary 2.4;
a consistency query may also return empty, which has no attained entry.
For every nonempty finite answer, the unsolved optimization task is to terminate with the exact $M$, a finite depth
$h_*$ with $m_{h_*}=M$, and a justified all-depth lower bound excluding every
smaller field, together with the source-total effective rank encoder and lawful
current-register consumer of Theorem 2.2. The installed data must depend only
on declared common input, and the actual encoder must be evaluated on the
acquired source before the complete cut. Existence of $h_*$ is not its uniform
synthesis, and no supplied-budget decision replaces this task.

A sufficient unresolved route is a complete fixed-set chooser: for each
nonempty $B\subseteq A$, return either a finite $H_B$ with $\neg J_B(H_B)$,
or valid all-depth persistence evidence with an effective procedure returning,
for every $h$, actual finite sources in the respective $D_r$ that agree through
$h$. Every returned source must preserve the entire old row, every literal,
each reached signed relation and off-task constraint, and its exact full target
row, on that source's same original root and legal acquisition. A limit satisfying
some positive equations, without these finite realizations, is insufficient.
Once persistence is proved, NSF's positive finite queries can produce each
requested witness; the missing step is the terminating, sound and complete
choice of that branch for arbitrary signed input. No particular finite form of
persistence certificate is assumed complete.

For one fixed $B$, the exclusion branch only excludes that set. For every
$k$-set it certifies $M<k$ by taking their finite maximum. Deciding all sets
would yield the optimizer as proved in Theorem 3.2, while pairwise exclusion
alone addresses the special value $M=1$. Neither exclusion of a single set nor
a finite plateau certifies optimality. The native $D_3$ illustrates the distinction:
its four-set is excluded at depth three, but its persistent triple supplies the
separate lower bound $M=3$. These finite tests and examples do not solve the
general synthesis or prove that it is undecidable.

**产地。** This is one theory-only continuation of the signed full-recut
memory question. Its positive claims are the ordinary proofs and explicit finite
native witnesses above; the broader objective and its unresolved all-input
quantifiers remain open.

## 7. References

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[RDR]: RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_ROW_DEPTH_RECOVERY.md
[SPC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md

## 追加锚（本行以下为增补区）
