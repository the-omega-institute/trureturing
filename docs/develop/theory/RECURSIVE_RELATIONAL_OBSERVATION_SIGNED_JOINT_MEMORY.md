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
\operatorname{Rel}_e(u)\;:\\Longleftrightarrow\;
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
$A=f(D)$ is finite and nonempty. For $r\in A$ put $D_r=f^{-1}(r)$. For an
attained prefix $p$, set

$$
S_h(p)=\{r\in A:\exists u\in D_r\text{ with }p_h(u)=p\},
\qquad
m_h=\max_{p\ {\rm attained}}|S_h(p)| .
\tag{SJM.8}
$$

The sequence $m_h$ is nonincreasing. Let $M(D,Q)$ be the least cardinality of a
complete conditional field $E$ for which one source-total effective consumer,
using the handoff $(P,Q,R_P,H_0,H_{\rm rel},N,E(u))$, has a uniform finite number
of post-entry reads and returns $f(u)$.

**Theorem 2.2 (minimum complete field and static reduction).** Under
Assumption 1.3, if $A$ is finite and nonempty, then

$$
\boxed{
M(D,Q)=\min_{h\ge0}m_h
=\max_{\xi}\bigl|\{r\in A:\xi\in\overline{D_r}\}\bigr| .}
\tag{SJM.9}
$$

The closure is in the prefix topology of finite or infinite ordered trees. The
minimum is attained at a finite $h$. The same value holds when the consumer is
allowed every legal adaptive serial $\mathsf{ApplyRho}$ strategy, and when it is
restricted to static reads at the supplied epoch. This equality concerns only the
number of complete conditional field values; it does not identify an optimal raw
call, address-length or update price.

*Proof.* Let a proposed field have $m$ attained values and let its consumer use
at most $K$ reads. Fix one field value $e$. Between two replies, the consumer's
computation and update schedule are source-independent and terminate on every
source reaching that segment. Unrolling the reachable four-valued reply histories
therefore gives a finite tree. Across the $m$ values, only finitely many physical
addresses are submitted; let $h$ be the largest address length.

The original-address locality clause (SLH.74.7), including born and absent
positions, says that a reply at any declared epoch from an address of length at
most $h$ is determined by the inclusive original depth-$h$ table. Thus two
sources with the same $E$ value and the same $p_h$ produce the same adaptive
serial run and the same output. If one attained prefix $p$ meets $k$ different
rows, selecting one source from each of those strata forces $k$ different field
values. Hence $m\ge m_h\ge\min_jm_j$.

The argument did not assume the field was constant on rows: arbitrary effective
encodings are covered. It also did not remove serial competitors. It compresses
their finite update segments and then applies the existing actual-prefix bridge

$$
\text{uniform finite-read serial}
\Longleftrightarrow
\text{uniform finite-read static}
\Longleftrightarrow
\exists h\ \operatorname{PrefDet}(D,Q,h)
\tag{SJM.10}
$$

from [ARH, (ARH.2.3)][ARH].

For the converse, take any supplied $h$. The finite table $p\mapsto S_h(p)$ is
effectively computable by the whole-source fixed-depth queries of [NSF, Lemma
5.1][NSF] and the complete-row compiler [NPL, Lemma 5.2][NPL]. During the same
paid acquisition, compute the actual full row and retain

$$
E_h(u)=\text{the zero-based rank of }f(u)\text{ in the canonical list }S_h(p_h(u)).
\tag{SJM.11}
$$

The installed table depends only on the public retained input and $h$. A default
value outside the successful fiber makes this a source-total effective encoder;
it is not a hidden source selector. At the actual current epoch $N$, recover all
replies in $p_h(u)$ by the supplied current-register decoder [SLH, Theorem
2.2][SLH]. At most $2(2^{h+1}-1)$ physical reads suffice, with submitted address
length at most $h+\lceil N/2\rceil$. The consumer then looks up the rank and
returns the complete row. A prefix attaining $m_h$ realizes every rank below
$m_h$, so the conditional field has exactly $m_h$ values. This proves the first
equality in the other direction and gives a static consumer, hence a legal serial
one.

For the closure identity, if $k$ row strata share a completion point $\xi$, each
finite depth of $\xi$ is met by all $k$ strata, so $m_h\ge k$ for every $h$. In
the reverse direction, suppose $m_h\ge k$ for all $h$. Since $A$ is finite,
one $k$-element set of row labels occurs for arbitrarily large $h$. The finite
prefix tree of simultaneous witnesses is finitely branching and has a node at
every depth. König's lemma gives a compatible finite or infinite completion
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

*Proof.* Split the finite original prefix at depth $h$ and beyond every recorded
endpoint. [NSF, Lemma 5.1][NSF] gives the exact finite native query for each pair
of candidate row pieces, retaining the complete old row, every guard and every
signed whole-subtree comparison in both source copies. [NPL, Theorem 5.3][NPL]
returns the finite target-row list and an original finite witness when the image
is finite. Enumerating the finitely many attained prefix patterns and applying
those feasibility decisions computes every $S_h(p)$. The monotonicity and
stabilization statements are immediate. The final sentence is a quantifier
distinction: existence of a finite minimizer supplies an effective construction
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

**Theorem 3.2 (what the finite tests do and do not settle).** Every fixed
$J_{r_1,\ldots,r_k}(h)$ is decidable by a finite native feasibility test. The
question whether it holds for all $h$ is exactly the unsupplied stopping and
realization obligation for the minimum in (SJM.9).

*Proof.* Use independent whole-source copies of each finite row piece from
[NPL, Lemma 5.2][NPL], impose equality of every reply at words of length at most
$h$, and retain all old classes, off-task disequalities, signed endpoint guards
and complete target partitions. The variable-rank navigation cases and
scalar-preserving mixed-image reduction of [NIC, Proposition 5.3][NIC] terminate
on this finite query and produce actual finite witnesses in both directions.

For a finite image, failure of all-depth contact for every $k$-tuple would give a
finite exclusion depth for each tuple, and the maximum of those finitely many
depths would give a determining prefix. Conversely, one persistent tuple gives
failure of every determining depth. What is absent is a terminating procedure
that, for an arbitrary input, chooses between a finite exclusion depth and a
source-faithful family of finite witnesses for every depth while preserving the
whole signed input. A sequence of finite positive answers, a limit partition, a
prescribed-budget certificate or a supplied guarded description does not perform
that quantifier exchange. No undecidability claim follows from this missing
procedure. This is the open stopping boundary recorded in [NPL, §10][NPL] and
[ARH, Definition 9.1][ARH]. $\square$

An observed plateau of the computable values $m_h$, finitely many tests, or a
valid supplied guarded certificate at a prescribed budget does not prove that
no later depth lowers the value. The complete-handoff premise and the finite
realization of every positive witness remain required at every finite stage.

## 4. Two actually acquired native fibers

The next construction is a native simultaneous-contact separation. Both inputs
use the same one-hole root row, the same target cut, the same original root and
register, and the same paid producer implementation. Their public signed schedules
differ only by the listed negative records. All witnesses below are finite actual
sources; no negative is tested only at a limiting completion.

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

The four target holes contain $z,y,\rho y,Fy$. Their first three values are
pairwise unequal by (SJM.4), so the only possible complete partitions are those
in (SJM.19), according to which of the three is selected by $z$. The choices
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

*Proof.* First record the finite witnesses used for contact. The atomic trees
$T_n$ agree on every fixed finite original prefix once $n$ is sufficiently
large. The three sources

$$
U(T_n,T_n),\quad U(T_n,T_{n+1}),\quad U(T_n,T_{n+2})
\tag{SJM.27}
$$

have rows $r_0,r_1,r_3$ respectively, and all retained signs hold by the
clock. This gives the three contacts among $r_0,r_1,r_3$ in $D_3$.

For the remaining contacts use the two finite prefix-growing contexts
$F(t)=\langle\beta,\rho t\rangle$ and $B(t)=\langle\alpha,t\rangle$. The
standard finite witness calculation for the native recurrence gives
$F^n(\beta)\to K$ with $F(K)=K$, and $B^n(\beta)\to J$ with $B(J)=J$;
these are prefix limits only. The triples

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

Both inputs are produced by the same paid ARH traversal and comparison procedure,
with the same original root, register and final epoch. Their signed records are
actual outcomes of reached endpoint comparisons; no arbitrary graph or compactness
model replaces the source-fiber directions. The off-diagonal Boolean contact
matrix is the complete graph $K_4$ in both cases, while the simultaneous contact
number, and hence the minimum field, differs. $\square$

**Proposition 4.6 (attained encoders and current-epoch consumers).** The value
three in $D_3$ is attained by a three-value complete field, and the value four in
$D_4$ by a four-value complete field.

*Proof.* For $D_3$ use $h=3$ in (SJM.11). The producer has the complete finite
source description already paid for by Proposition 2.1, computes its full row
and stores its rank in the canonical $S_3(p_3(u))$ list. Proposition 4.5 shows
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

This outcome is attained. After a complete successor handoff retaining this
read and the original input, the source fiber is

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
four-row image is preserved. The inclusive original depth-two replies of the
$z$-subtree distinguish the three templates in (SJM.30) from every other finite
$z$: the root, child replies and the absent replies below the two leaves identify
$\alpha$, $\beta$ and $\langle\beta,\beta\rangle$; a deeper finite tree cannot
have the same depth-two table. Every remaining finite tree is therefore in
$r_3$. Thus $m_2=1$ and Theorem 2.2 gives (SJM.34). At the actual epoch one, the
supplied current-register decoder obtains the depth-two replies in at most
$2(2^3-1)=14$ further reads, then returns the complete exterior and partition.

If the old three-value field is retained, its old decoding table remains valid
on the refined fiber and still gives a correct service. It is no longer optimal.
A new complete successor cut may instead discard it and install the constant
one-value field justified by (SJM.30). That replacement is a paid computation
from the actual acquired continuation state; it is not a free reinterpretation
of the old rank. $\square$

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

for every old code value $e$. In particular, $M(D',Q)\le M(D,Q)$ whenever both
images are finite.

*Proof.* A known update changes only the physical register from $\rho^M u$ to
$\rho^{M+k}u$; it does not change the original source or the declared target.
[SLH, Theorem 2.2][SLH] converts each needed original prefix to reads at the
new actual epoch, so no old-version read or reset is inserted. If a decoder was
interrupted by an update, its bounded query list is restarted at the new
certified epoch; replies from different epochs are not spliced.

The new reply restricts every code fiber as shown in (SJM.31). Restricting a
source domain cannot increase the number of rows meeting an attained prefix, so
Theorem 2.2 gives the inequality. The observer must retain the old code value
and any code-dependent path/control state when it refines the fiber; using only
$D'$ while forgetting $e$ would describe a larger state than the actual handoff.
A newly optimal code requires a separately paid complete preparation unless the
retained continuation already supplies its determining prefix and row table.
Changing $Q$ changes the target and requires a new sufficiency argument. $\square$

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
finite sources and finite signed guards in both directions. Proposition 3.2
leaves exactly the all-depth choice between a finite exclusion depth and a
source-faithful productive witness family. No statement here removes that
choice. The remaining claims are therefore outside the proved scope. $\square$

**文献与来源表态。**

| 来源 | 精确转移与边界 |
| --- | --- |
| [ARH, §§1–3, (ARH.2.3)](RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md) | `repo-derived`: complete signed source fiber, paid same-root producer, endpoint guards, current register and static/serial prefix bridge. It does not supply a uniform optimizer for arbitrary signed input. |
| [SLH, §§2, 59–75](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md) | `repo-derived`: actual original-address locality and current-epoch decoding, including born and absent positions. It does not turn a finite test sequence into an all-depth stopping certificate. |
| [NPL, §§5–6](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md) | `repo-derived`: exact finite/infinite complete-row image decision and original finite witnesses. A finite image does not by itself reveal a determining depth. |
| [NSF, Lemma 5.1](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md) | `repo-derived`: fixed-depth whole-source native feasibility with designated ranks, all old constraints and both endpoint copies. It does not decide the all-depth quantifier. |
| [NIC, Proposition 5.3](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md) | `repo-derived`: mixed interpreted-$\rho$ navigation and finite-depth signed feasibility. Its finite image cover is not a uniform synthesis theorem for arbitrary signed contacts. |
| [RDR, Theorem 6.2](RECURSIVE_RELATIONAL_OBSERVATION_RETAINED_ROW_DEPTH_RECOVERY.md) | `repo-derived overlap`: conditional rank coding for retained-row intrinsic depth. The present target is a signed full original recut and its native joint examples. |
| [SPC, §§2–5](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_PRODUCTIVE_CONTACT.md) | `repo-derived`: finite productive signed witnesses and the discipline that every negative is checked on actual finite approximants. Supplied certificates are sufficient evidence, not complete stopping decisions. |
| `D5/S0/History/Coding/MinimumRollbackAlphabet.minimum_rollback_alphabet` | Exact finite process-fiber lower bound and fiberwise attaining labels. At fixed $h$ take $X_h=\{(p,r):r\in S_h(p)\}$, $Y$ the finite set of attained prefixes, $U(p,r)=p$ and $L(p,r)=r$; the largest process fiber is exactly $m_h$. ARH/SLH supply acquisition and current-register decoding. |
| Charpenay–Le Treust–Roumy, *Optimal Zero-Error Coding for Computing under Pairwise Shared Side Information*, Definition III.1 and Theorem III.4, [arXiv:2211.03649](https://arxiv.org/abs/2211.03649) | `literature-attested`: the one-shot support/colouring intuition. Only the finite zero-error colouring correspondence transfers; asymptotic rates, stochastic sources and free side information do not. |
| Barguñó–Creus–Godoy–Jacquemard–Vacher, *Decidable Classes of Tree Automata Mixing Local and Global Constraints Modulo Flat Theories*, Theorem 5.22 and Corollaries 5.23–5.24, [arXiv:1302.6960](https://arxiv.org/abs/1302.6960) | `literature-attested`: emptiness for their constrained-tree-automaton classes. No faithful translation of arbitrary interpreted mixed-epoch $\rho$ histories or the unbounded joint-prefix obligation is assumed. |
| Milius–Moss, *The category theoretic solution of guarded recursive equations*, Theorem 7.15 | `literature-attested`: guarded recursive solutions in a contracting/complete setting. It does not certify that finite signed approximants preserve this native source fiber or that a finite productive description is complete. |
| PR15621 at `0487ddfee131db56e40b654fad5a69689948e3c7` and PR15653 at `c0f820f0b4800326b5c9d06b23f11ce925b404fb` | Published overlap only: supplied-coordinate closure and guarded-description equality. They are not premises for arbitrary stopping or universal certificate completeness. |
| Retained literal root-depth manuscript, merged at `3508d303746985c18ca446a13c92b5c22f9df10d` | Static root target and specified normal-code continuation. It is distinct from this signed mixed-epoch full-row target. |

The supplier pin for this volume is the merged integration baseline
`21dc7376d6bf6518ffd95621637dd6bb1ee8764d`. No external literature or repository
source cited here is being promoted to a kernel-certified premise.

**开放问题 6.2 (terminating signed joint synthesis).** For every arbitrary
attained finite signed input and every finite set of complete row labels, decide
between

1. a finite depth excluding all joint contacts of that set, and
2. an effective source-faithful family of finite witnesses at every depth,
   preserving the old complete row, every literal and guard, every signed
   equality/disequality, the same-source coupling and the complete target rows.

A solution must return the minimizing depth and the rank encoder when the first
alternative occurs, or a valid all-depth witness mechanism when the second does.
The finite tests, decreasing sequence $m_h$, and the two native fibers above do
not supply this completeness result. Failure to find such a procedure is not an
undecidability theorem.

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
