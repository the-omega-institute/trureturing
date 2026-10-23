# Native complete records with unknown unbounded epochs

This volume gives an exact effective description of the chronological
realization fiber in [NAR, Proposition 12.6][NAR]. The sources remain all
nonempty finite ordered native trees. The essential additional statement
is that the truth of each fixed complete row eventually stabilizes on
every individual original source, at a threshold computed from the row.
Consequently a finite family of fixed-epoch predicates represents both
the entire unbounded epoch fiber and every original-source fiber.

The arguments are ordinary mathematical proofs, not new Lean-verified
declarations. The fixed-epoch decision and witness theorem is reused from
[NSF, Theorem 5.2][NSF]. A decision procedure specified mathematically is
distinct from an implemented solver and from a physical observation
procedure. The broader mutual-recovery problem for space, time, boundary
and memory retains the additional obligations in Section 8.

## 1. Exact proposed records and the common-source relation

**Definition 1.1 (native domain and supplied operations).** Write

$$
\begin{aligned}
\mathcal T&::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,\\
\rho\alpha&=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle,\\
T_j&=\rho^j\alpha\quad(j\in\mathbb N).
\end{aligned}
\tag{NUE.1}
$$

The constructors are free, ordered and literal. Every member of
$\mathcal T$ is finite and has at least one leaf. Addresses are finite
$L/R$ words, with root $\varepsilon$. A finite cut $P$ is prefix-free;
the empty cut and the root singleton are allowed. The complete record
$R_P(u)$ is precisely [NAR, Definition 1.2][NAR]: the exterior with
address-marked reached holes and its complete equality partition of
the hidden whole subtrees. Two different partition classes assert
disequality. A blocked requested address retains its concrete blocking
leaf. No comparison between a hidden value and a concrete exterior value,
and no comparison between different captures, is added to this record.

The all-source injectivity, reached-subtree transport and branch-saturation
facts are reused from [NSF, Lemma 9.2][NSF]. In particular, for every
$h\ge0$ and $t\in\mathcal T$, every reply through depth $h$ in
$\rho^n t$ is branch when $n\ge2(h+1)$. An address reached in a tree
remains reached, and its subtree after $k$ further updates is the
$\rho^k$-image of its former value. This statement can be applied with
any actual capture as its starting tree; it does not transport an
absent subtree backward through its birth.

**Definition 1.2 (finite validation of a proposed row).** A proposed row
$R=(C,\pi)$ at $P$ is valid when all the following finite conditions hold.

1. $C$ is a nonempty finite ordered full binary context whose leaves are
   $\alpha$, $\beta$, or addressed holes. Each hole label is its actual
   address in $C$, appears once, and belongs to $P$. Let $H$ be this
   set of hole addresses.
2. For every $p\in P\setminus H$, some concrete leaf of $C$ has an
   address that is a strict prefix of $p$.
3. $\pi$ is an equivalence relation on exactly $H$, specifying the
   equality or disequality of every pair in $H$. Equivalently, it is a
   partition of $H$, with no omitted pairwise information.

These conditions reject, for example, a concrete leaf at a requested
cut position: such a position is reached and must have been replaced by
a hole. They also reject a hole at a falsely claimed address, missing
blockers, and an incomplete or inconsistent partition. Validating an
input does not assume joint realizability with another input. Class
names have no meaning beyond their partition and can be ordered by
their least hole addresses.

**Proposition 1.3 (using the complete-row filling supplier on proposed
data).** Validation in Definition 1.2 characterizes the rows that can
occur individually. For a valid row, let $\mathcal B=H/\pi$, and let
$C[\mathbf z]$ replace each hole $p$ by $z_{[p]}$. The supplied
complete-row filling equivalence becomes

$$
R_P(u)=R
\quad\Longleftrightarrow\quad
\exists (z_b)_{b\in\mathcal B}\in\mathcal T^{\mathcal B},\qquad
u=C[\mathbf z]\ \land\
\bigwedge_{b\ne c}z_b\ne z_c.
\tag{NUE.2}
$$

For a fixed $u$, the displayed class valuation is unique. When there
are no holes, the valuation is the unique empty tuple.

Proof. An actual row has the stated syntax and blockers by its
definition. Conversely choose distinct finite trees for the finitely
many classes, for example distinct $T_j$, and fill $C$. Every hole
is then reached at its stated cut address. Every other cut address
remains blocked by its stated strict-prefix concrete leaf. The exterior
is exactly $C$, and the chosen distinct class values give exactly
$\pi$. Thus validation supplies an individual representative, without
an assumption that different rows share a representative.

Now apply the existing filling correspondence [NAR, (NAR.1.4)][NAR]
or [NativeCutFibers, `rowFiberEquiv`][CUT] to this representative.
Its hypotheses include all different-class disequalities. The inverse
reads the value at a representative hole of each class. This is a
mathematical inverse on supplied trees, not an extra observation port.
The independent addressed record is identified with canonical row
syntax by [ActualCutPartitionDecoder, `canonicalRow_record_iff`][ROW].
No new filling theorem is needed beyond this proposed-data validation.
$\square$

**Definition 1.4 (the exact joint problem).** For $m\ge1$, the input is
an ordered tuple $(P_i,R_i)_{i<m}$. Define the chronological cone,
the source fibers, and their joint relation by

$$
\begin{aligned}
\mathcal C_m&=\{\mathbf n\in\mathbb N^m:0=n_0\le\cdots\le n_{m-1}\},\\
F_{\mathbf n}&=\{t\in\mathcal T:
        \forall i<m,\ R_{P_i}(\rho^{n_i}t)=R_i\},\\
\mathscr H&=\{(\mathbf n,t):\mathbf n\in\mathcal C_m,
                                      \ t\in F_{\mathbf n}\},\\
E&=\{\mathbf n\in\mathcal C_m:F_{\mathbf n}\ne\varnothing\}.
\end{aligned}
\tag{NUE.3}
$$

This is the fiber of [NAR, Proposition 12.6][NAR]; for $m=2$ it is
the lag fiber of NAR Proposition 10.3, with its first coordinate zero.
The same $t$ appears in every conjunct. Each exponent is an unbounded
natural, and equal epochs are permitted. If any row fails validation,
$\mathscr H$ and $E$ are empty. No nonempty-fiber premise is used below.

For later use, the exact formula for $t\in F_{\mathbf n}$ is

$$
\exists (\mathbf z_i)_{i<m}\quad
\bigwedge_{i<m}\left(
 \rho^{n_i}t=C_i[\mathbf z_i]\ \land\
 \bigwedge_{b\ne c}z_{i,b}\ne z_{i,c}\right).
\tag{NUE.4}
$$

Class names from different rows are separate variables. Their only
implicit connection is the common whole original $t$ and its iterates.
At supplied numeral epochs this formula is directly in the scope of
NSF Theorem 5.2. With free epochs it is a semantic definition, not a
claim that NSF already accepts quantified powers.

## 2. Stabilization of equality to one fixed complete row

**Definition 2.1 (a row-dependent threshold).** For a valid $(P,R)$,
write $R=(C,\pi)$ and put

$$
b(P,R)=
\begin{cases}
2(d+1),&\text{if }C\text{ has a concrete leaf, with least such depth }d,\\
2D,&\text{otherwise, where }D=\max(\{0\}\cup\{|p|:p\in P\}).
\end{cases}
\tag{NUE.5}
$$

Both depths are computed from the finite supplied syntax. The first
case uses the shallowest concrete exterior leaf, including a blocking
leaf; it does not use the unknown hidden subtrees. These are sufficient
thresholds, without a minimality assertion.

**Theorem 2.2 (sourcewise eventual truth of a fixed row).** For every
valid $(P,R)$, every $t\in\mathcal T$ and every $n\ge b=b(P,R)$,

$$
R_P(\rho^n t)=R
\quad\Longleftrightarrow\quad
R_P(\rho^b t)=R.
\tag{NUE.6}
$$

Consequently the same equivalence holds between an arbitrary $n$ and
$\min(n,b)$. The original source on the two sides is identical.

Proof. Suppose first that $C$ contains a concrete leaf at depth $d$.
If $R_P(\rho^n t)=R$, that leaf is a literal leaf of $\rho^n t$ at
the same address. But NSF Lemma 9.2 says every address at depth at
most $d$ is a branch for $n\ge2(d+1)$. Thus the equality is false
for every such $n$ and every $t$, including $n=b$. This does not
require the proposed row to occur anywhere along the orbit of $t$.

Suppose next that $C$ has no concrete leaves. All its leaves are
holes. Validation forces $H=P$: an omitted member of $P$ would
require a concrete blocker. Hence $P$ is the entire leaf frontier of
the finite full context $C$. In particular it covers every infinite
binary ray, and its proper prefixes are exactly the internal nodes
of $C$. This is a consequence of the row syntax, not a promise that
the original arbitrary cut was complete.

If $D=0$, $P=\{\varepsilon\}$ and $C$ is the single root hole.
Its partition is necessarily the singleton partition. Its row is
constant on all nonempty sources, and $b=0$ works. If $D>0$, apply
NSF Lemma 9.2 with $h=D-1$. At epoch $2D$ all proper prefixes of
members of $P$ are branches. Every $p\in P$ is therefore reached.
Cutting at these positions yields exactly the frontier context $C$,
with no concrete exterior leaves. The same is true at every later
epoch.

Let $v=\rho^{2D}t$. Each cut position now exists. For $k\ge0$,
reached-subtree transport and injectivity give, for all $p,q\in P$,

$$
 (\rho^k v)|_p=\rho^k(v|_p),\qquad
 (\rho^k v)|_p=(\rho^k v)|_q
 \ \Longleftrightarrow\ v|_p=v|_q.
\tag{NUE.7}
$$

Thus every equality bit, and also every disequality bit, is unchanged.
The entire addressed exterior and the complete partition agree at
epochs $2D$ and $2D+k$. They either both equal the proposed row or
both fail to equal it. Transport has only been used after the cut
positions are known to exist. This proves (NUE.6). For $n<b$ the
minimum leaves $n$ unchanged. $\square$

**Proposition 2.3 (the stabilized object and its scope).** Theorem 2.2
stabilizes the predicate of equality to one supplied finite row. It
does not assert that $n\mapsto R_P(\rho^n t)$ is eventually constant
for every cut. It does not impose an upper bound on a feasible epoch.

Proof. With $P=\varnothing$ and $t=\alpha$, the output is the full
tree $T_n$. These are pairwise distinct by NSF Lemma 9.2. Every fixed
finite proposed output nevertheless eventually fails, as in the first
case of Theorem 2.2. With $P=\{\varepsilon\}$, the single-hole row
holds at every epoch. Its threshold zero is a truth threshold, not
a bound on actual time. $\square$

The atomic-orbit index compiler [ARH, Theorem 5.2][ARH] already uses
eventual whole-row truth after its designated relation has forced the
source to be some $T_k$. That restricted supplier is retained. The
quantifiers in (NUE.6) instead keep every arbitrary finite $t$ and
preserve that very $t$ while changing its epoch.

## 3. A finite exact representation of every unbounded history

**Definition 3.1 (common cap and finite representatives).** For valid
input put

$$
\begin{aligned}
B&=\max\bigl(\{1\}\cup\{b(P_i,R_i):i<m\}\bigr),\\
\kappa_B(\mathbf n)_i&=\min(n_i,B),\\
A_B&=\{\mathbf c\in\mathbb N^m:0=c_0\le\cdots\le c_{m-1}\le B\},\\
L_{\mathbf c}&=\{\mathbf n\in\mathcal C_m:
                                       \kappa_B(\mathbf n)=\mathbf c\}.
\end{aligned}
\tag{NUE.8}
$$

The common $B$, rather than different coordinate caps, is used to
preserve chronology. The regions $L_{\mathbf c}$ are nonempty,
pairwise disjoint, and cover $\mathcal C_m$. Each contains its own
representative $\mathbf c$.

**Theorem 3.2 (equality of entire source fibers).** For every
$\mathbf n\in\mathcal C_m$,

$$
F_{\mathbf n}=F_{\kappa_B(\mathbf n)}.
\tag{NUE.9}
$$

Proof. Fix an arbitrary $t\in\mathcal T$. If $n_i<B$, its coordinate
is unchanged. Otherwise both $n_i$ and $B$ lie at or above
$b(P_i,R_i)$. Apply Theorem 2.2 twice to this same $t$, obtaining
equivalence of the $i$th row predicate at $n_i$ and $B$. Conjoin over
all $i$. The nondecreasing map $n\mapsto\min(n,B)$ preserves order
and fixes zero, so the capped tuple lies in $A_B$. No existential
source has been selected or replaced in this argument. $\square$

**Theorem 3.3 (effective joint support, negative termination and finite
witnesses).** There is a terminating mathematical procedure which, on
valid input of Definition 1.4, returns $B$ and a finite set
$K\subseteq A_B$ such that

$$
\begin{aligned}
K&=\{\mathbf c\in A_B:F_{\mathbf c}\ne\varnothing\},\\
E&=\coprod_{\mathbf c\in K} L_{\mathbf c},\\
\mathscr H&=\coprod_{\mathbf c\in K}
                         (L_{\mathbf c}\times F_{\mathbf c}).
\end{aligned}
\tag{NUE.10}
$$

The product uses the same finite original source throughout each
history. Each $F_{\mathbf c}$ has its exact fixed-epoch predicate
(NUE.4); it is not replaced by a finite sample. The procedure decides
emptiness and can return one finite source $t_{\mathbf c}$ for each
accepted representative. That same source realizes every epoch tuple
in $L_{\mathbf c}$.
Invalid data return the empty representation, for example $B=1$ and
$K=\varnothing$.

Proof. Reject invalid proposed rows by Definition 1.2. For valid rows,
compute $B$ and enumerate $A_B$. The number of representatives is

$$
|A_B|=\binom{B+m-1}{m-1},
\tag{NUE.11}
$$

the number of nondecreasing lists of length $m-1$ selected with
repetition from $0,\ldots,B$.

At each representative $\mathbf c$, call NSF Theorem 5.2 directly
on the first complete row at epoch zero and all the additional
complete-row tests at the supplied numeral epochs $c_i$. Equivalently,
use (NUE.4) with those numerals, including every different-class
disequality. The theorem decides emptiness without an inhabitation
promise and returns a finite original on a positive answer. Mark
precisely these representatives as members of $K$. All calls concern
one original variable shared by every record. Zero hidden classes
produce ground contexts and empty valuation lists, not a missing case.

For soundness, a returned $t_{\mathbf c}\in F_{\mathbf c}$ belongs
to $F_{\mathbf n}$ for every $\mathbf n\in L_{\mathbf c}$, by
Theorem 3.2. This preserves its concrete exterior, every blocking
leaf, every reached hole and every partition bit at each capture.
For completeness, an arbitrary unbounded realizing pair
$(\mathbf n,t)$ has $\mathbf c=\kappa_B(\mathbf n)\in A_B$ and
$t\in F_{\mathbf c}$. Therefore that finite representative is
accepted. Applying the same equality to every $t$ proves the third
line of (NUE.10), which is stronger than preservation of existential
support alone.

All parsing, threshold calculations and representative enumeration
are finite. There are exactly (NUE.11) total fixed-epoch decisions
in the exhaustive construction. If every representative is rejected,
completeness proves that no unbounded tuple has a finite shared
original. This is the terminating NO case. It does not infer
emptiness from a finite unsuccessful search for trees or epochs.

If $K\ne\varnothing$, choose any accepted representative and its
returned finite source. To answer a query at an arbitrary supplied
tuple $\mathbf n$, first check chronology and compute its cap.
Reject if that cap is absent from $K$; otherwise return the stored
source for the cap, or regenerate one by its fixed-epoch call. No
iteration up to the size of $\mathbf n$ is needed for this selection.
Actually materializing or executing $\rho^{n_i}t_{\mathbf c}$ is
a separate finite, potentially much larger operation. $\square$

**Corollary 3.4 (explicit linear regions).** The representation of
$E$ in Theorem 3.3 is an effective finite union of linear sets in
$\mathbb N^m$. More specifically, if $c_i<B$ for all $i$, then
$L_{\mathbf c}=\{\mathbf c\}$. Otherwise let $k$ be the first
index with $c_k=B$, and define $v_j\in\{0,1\}^m$ to be one in
coordinates $j,\ldots,m-1$ and zero before $j$. Then

$$
L_{\mathbf c}=\mathbf c+
                  \sum_{j=k}^{m-1}\mathbb N v_j.
\tag{NUE.12}
$$

In particular an exact quantifier-free arithmetic description is

$$
\mathbf n\in\mathcal C_m\quad\land\quad
\bigvee_{\mathbf c\in K}
\left(
 \bigwedge_{c_i<B} n_i=c_i\ \land\
 \bigwedge_{c_i=B} n_i\ge B
\right).
\tag{NUE.13}
$$

Proof. Monotonicity of $\mathbf c$ makes its entries equal to $B$
one terminal suffix. Since $B\ge1$ and $c_0=0$, $k\ge1$. For a
tuple in the cap region put
$a_k=n_k-B$ and $a_j=n_j-n_{j-1}$ for $j>k$. These are natural,
and direct substitution gives
$\mathbf n=\mathbf c+\sum_{j=k}^{m-1}a_jv_j$. Conversely every
such sum has the required fixed prefix, nondecreasing tail and cap.
The case with no capped coordinate is immediate. This proves
semilinearity by an explicit construction; no regularity or
Presburger hypothesis about native fibers has been assumed.
$\square$

**Corollary 3.5 (complete lag fibers and individual relative counts).**
For two records the lag fiber is exactly an effectively computed
subset of $\{0,\ldots,B-1\}$, optionally together with
$\{B,B+1,\ldots\}$. It is finite or cofinite. This conclusion
holds on the full native source domain of Definition 1.1.

For arbitrary $m$, $E$ is finite exactly when no accepted representative
has a coordinate equal to $B$; in that case $|E|=|K|$. On nonempty
input the whole epoch tuple is unique exactly when $K$ consists of
one representative and that representative has no capped coordinate.
For fixed $0\le a<b<m$, the exact possible values of $n_b-n_a$ are
also effectively a finite set, optionally together with one terminal
integer interval.
Every capped coordinate of an accepted representative belongs to a
ray-covering cut, and is consequently an isolated vertex of the NAR
overlap graph.

Proof. The first assertions follow from (NUE.12). For the relative-count
assertion, on an
uncapped region the difference is $c_b-c_a$. On a region with first
capped index $k>b$, both coordinates are fixed and the same is true.
If $k\le b$, the coefficient of a generator $v_j$ in this difference
is one precisely when $a<j\le b$, and zero otherwise. At least one
such $j$ lies in $\{k,\ldots,m-1\}$, namely
$\max(k,a+1)$. Its coefficient can be any natural. Thus the image
of that region is exactly $\{c_b-c_a,c_b-c_a+1,\ldots\}$. Take
the finite union over $K$. These particular difference projections
need no unproved claim about arbitrary arithmetic projections.
Finally, a row with a concrete leaf is impossible at epoch $B$ by
the first case of Theorem 2.2. Thus an accepted capped coordinate has
only holes in its exterior, and the second case proves that its cut
covers every ray. Its visible-cell set is empty. The cap therefore
does not alter any clock difference on an overlap edge.
$\square$

## 4. Which time and source values the records determine

**Theorem 4.1 (effective original-source uniqueness).** After deciding
$E\ne\varnothing$, it is decidable whether the original finite tree
value is the same in every realizing history, even when their epoch
tuples differ. If it is the same, its value is effectively recoverable.
Otherwise two distinct finite originals with realizing chronological
tuples can be returned.

Proof. By (NUE.10), the set of possible originals is exactly

$$
U=\bigcup_{\mathbf c\in K}F_{\mathbf c}.
\tag{NUE.14}
$$

Obtain one witness $t_*$ from an accepted representative. For every
$\mathbf c\in K$, use NSF Theorem 5.2 on its entire fixed-epoch
predicate together with the native disequality $t\ne t_*$. Here
$t_*$ is a supplied finite ground term, so every query remains within
the original supplier's language. If one succeeds, its returned
$t'$ and that representative form a second history, with
$t'\ne t_*$. If all fail, every element of every $F_{\mathbf c}$
equals $t_*$, so $U=\{t_*\}$. This adds at most $|K|$ total
fixed-epoch queries after one witness is available. It neither invokes
a new variable-power decision nor enumerates a bounded tree universe.
$\square$

**Corollary 4.2 (conditional recovery and its converse).** Suppose the
rows really were acquired from one finite original and one chronological
pure-$\rho$ history with the stated cut semantics. Then its actual
relative epoch tuple belongs to $E$ and its original belongs to $U$.
A singleton $E$ therefore recovers its exact update counts; a singleton
$U$ recovers its exact original tree value. Conversely, if two realizations
have different values of one of these targets, no deterministic function
of only the same supplied records can identify that target correctly
on both realizations.

The same original-source uniqueness criterion decides uniqueness of
the pair consisting of its canonical boundary measure and scale, and
of its complete primitive-root/depth coordinates. These are original
source values, not an independently acquired current scale or epoch.

Proof. The acquisition hypothesis places the actual history in
$\mathscr H$. Singleton fibers give the stated identifications;
two different target values at the same input defeat any one-valued
decoder on that input. Nonemptiness is checked first, so uniqueness
is never inferred vacuously from an impossible record tuple.

The supplied full-tree primitive-root/depth representation is injective
and reconstructs its source; see [IntrinsicSubstitutionCoordinates,
`intrinsic_coordinates`][INTR] and [ABC, Section 2][ABC]. The supplied
boundary representation $t\mapsto(\nu_t,W(t))$ is injective with
effective reconstruction on its attained image, by [Boundary IV,
Theorem 113.5][BOUNDARY]. Consequently either complete coordinate pair
is constant on $U$ exactly when $U$ is a singleton. When this holds,
compute the pair from the recovered finite $t_*$. Boundary measure
alone is a different target: it forgets substitution phase, and scale
or epoch evidence is not supplied for free. $\square$

**Proposition 4.3 (semantic identification does not authenticate an
event).** Neither acceptance nor uniqueness in Theorems 3.3 and 4.1
certifies the physical identity of a register or an alleged past
acquisition or execution.

Proof. The decision input is the same finite tuple whether it was
truthfully acquired, copied from another register with the same tree
value, or written without an acquisition. A function of that tuple
has the same result in these situations. The latter distinctions are
not predicates of its semantic input. The acquisition and continuity
premises in Corollary 4.2 cannot be deduced from its output. $\square$

## 5. A finite native obstruction to pairwise gluing

**Proposition 5.1 (compatible overlap clocks and all pairs, but no
common finite original).** There are three complete native records
whose overlap graph is complete and whose overlap-clock differences
are all zero, such that each pair is realized at equal epochs by one
finite original, but the triple has empty $E$. Every record has three
distinct hidden classes. Removing any one record removes the
obstruction.

Proof. Use the following cuts and literal addressed exteriors:

$$
\begin{aligned}
P_0&=\{LL,LRLL,LRLR,LRR\},\\
C_0&=\left\langle
 \left\langle\square_{LL},
   \left\langle\left\langle\square_{LRLL},\square_{LRLR}\right\rangle,
                 \square_{LRR}\right\rangle\right\rangle,\alpha
 \right\rangle,\\
P_1&=\{LL,LRL,LRRL,LRRR\},\\
C_1&=\left\langle
 \left\langle\square_{LL},
   \left\langle\square_{LRL},
                 \left\langle\square_{LRRL},\square_{LRRR}\right\rangle
   \right\rangle\right\rangle,\alpha\right\rangle,\\
P_2&=\{LLL,LLR,LRL,LRR\},\\
C_2&=\left\langle
 \left\langle\left\langle\square_{LLL},\square_{LLR}\right\rangle,
               \left\langle\square_{LRL},\square_{LRR}\right\rangle
 \right\rangle,\alpha\right\rangle.
\end{aligned}
\tag{NUE.15}
$$

The partitions, in class order, are

$$
\begin{aligned}
\pi_0&=\bigl\{\{LL,LRLL\},\{LRLR\},\{LRR\}\bigr\},\\
\pi_1&=\bigl\{\{LL\},\{LRL,LRRL\},\{LRRR\}\bigr\},\\
\pi_2&=\bigl\{\{LLL,LRR\},\{LLR\},\{LRL\}\bigr\}.
\end{aligned}
\tag{NUE.16}
$$

Within each displayed partition every two different classes are
required to have unequal values. Set
$d=\langle\alpha,\beta\rangle$,
$e=\langle d,\beta\rangle$, and

$$
S(A,B,C)=\left\langle\left\langle A,\langle B,C\rangle\right\rangle,
                                      \alpha\right\rangle.
\tag{NUE.17}
$$

The three pair witnesses, each with seven leaves, are as follows.
The class-value columns use exactly the class orders in (NUE.16).

| Records | Original at both epochs zero | Values for first row | Values for second row |
| --- | --- | --- | --- |
| $0,1$ | $S(\alpha,d,e)$ | $(\alpha,\beta,e)$ | $(\alpha,d,\beta)$ |
| $0,2$ | $S(d,e,\alpha)$ | $(d,\beta,\alpha)$ | $(\alpha,\beta,e)$ |
| $1,2$ | $S(e,\alpha,d)$ | $(e,\alpha,\beta)$ | $(d,\beta,\alpha)$ |

Substitution into (NUE.15) checks the entire exterior. Each displayed
class triple is pairwise distinct, by leaf label or by being a leaf,
a two-leaf tree, or a three-leaf tree. Hence these witnesses satisfy
all disequalities, not merely the repeated-class equalities.

For the overlap calculation, each $P_i$ covers exactly the left
root cylinder. Its visible cells in [NAR, Definition 12.2][NAR] are
exactly the depth-four words starting with $R$. These sets coincide
and are nonempty. Every row exposes the identical concrete right
subtree $\alpha$. Thus every shared visible-cell clock agrees and
every edge difference is zero. The overlap equations admit the
chronological tuple $(0,0,0)$.

Now suppose one original realizes the triple. Row zero forces a
literal $\alpha$ at $R$. Homomorphic transport preserves this
address and makes its later value $T_{n_i}$. Rows one and two again
expose $\alpha$ there. Since $T_j=\alpha$ only for $j=0$, both
later epochs are zero. The three exteriors therefore concern one
unchanged tree $S(A,B,C)$. They require $A,B,C$ all to be branches
where their children occur, and their repeated classes impose

$$
A=B|_L,\qquad B=C|_L,\qquad C=A|_L.
\tag{NUE.18}
$$

Let $\ell(x)$ be the positive finite number of leaves of $x$.
Being the left child of a full binary tree strictly lowers that
number. Equation (NUE.18) yields

$$
\ell(A)<\ell(B)<\ell(C)<\ell(A),
\tag{NUE.19}
$$

which is impossible. This proves the unbounded negative claim for
all finite originals, rather than only for the displayed witnesses.
$\square$

**Proposition 5.2 (the finite-tree and chronology content of the
obstruction).** The strict-subtree obstruction in Proposition 5.1
does not depend on an accidental contradiction among its concrete
markers. If the outside $\alpha$ anchor is removed, and every cut
address loses its initial $L$, the resulting three complete cuts
still have no joint chronological realization. Each pair, however,
is realized at every nonnegative lag by its corresponding six-leaf
original. Allowing cyclic infinite trees would invalidate the finite
occurrence argument, including its complete partitions.

Proof. Without the anchor, the cuts are
$Q_0=\{L,RLL,RLR,RR\}$,
$Q_1=\{L,RL,RRL,RRR\}$ and
$Q_2=\{LL,LR,RL,RR\}$.
They are complete frontiers. Each pair witness from Proposition 5.1
has all of its relevant holes already reached at epoch zero.
Homomorphism and injectivity preserve both complete rows at every
later epoch, establishing every lag for that pair.

In a hypothetical joint history, transport the row-zero equality
and the row-one equality to the third epoch. All addresses involved
were reached at the capture supplying each equality, so this use
of transport has its guards. At the third epoch define $A,B,C$ to
be the subtrees at $L,RL,RR$. The transported equalities and the
third row give (NUE.18) at that one epoch. The finite leaf-count
contradiction again applies, without forcing equal epochs.

To exhibit the forbidden change of domain, the guarded recursive
equations

$$
A=\langle C,\alpha\rangle,\qquad
B=\langle A,\beta\rangle,\qquad
C=\langle B,\langle\alpha,\alpha\rangle\rangle
\tag{NUE.20}
$$

unfold to rational infinite ordered trees satisfying (NUE.18).
Their right children show $A,B,C$ pairwise unequal. The three class
triples are respectively $(A,\beta,C)$,
$(A,B,\langle\alpha,\alpha\rangle)$ and $(C,\alpha,B)$;
each is pairwise distinct. Thus these infinite objects satisfy even
the full partitions. They are not elements of $\mathcal T$ and
cannot repair a finite-tree occurrence failure. This is a same-history
record construction, distinct from prefix contact among different
source strata. $\square$

## 6. Edge cases and the exact boundary of coordinate capping

**Proposition 6.1 (birth, empty classes and a genuinely unbounded
fiber).** At $P_0=P_1=\{L,R\}$, let $R_0$ be the concrete leaf
$\alpha$ with no holes and empty partition, and let $R_1$ have
exterior $\langle\square_L,\square_R\rangle$ and two distinct
classes. Then

$$
E=\{(0,n):n\ge2\},\qquad U=\{\alpha\}.
\tag{NUE.21}
$$

If the second row instead has one equality class, its fiber is empty.

Proof. The zero-class first row forces $t=\alpha$, with both
requested children blocked. $T_0=\alpha$ and $T_1=\beta$ still
block them. For $n\ge2$, the supplied atomic recurrence gives
$T_n=\langle T_{n-1},T_{n-2}\rangle$. Both holes are then reached
and their values are distinct. This proves both directions of
(NUE.21) and the assertion for the opposite partition. The same
finite original realizes every accepted lag. $\square$

**Proposition 6.2 (degenerate inputs and the dependence on the whole
row).** The representation includes all of the following cases.

1. For $m=1$, the only possible epoch tuple is $(0)$; it is accepted
   exactly when the row validates. If a zero-record input is admitted
   with vacuous chronology, its fiber is the singleton empty tuple
   and any finite original, for example $\alpha$, is a witness.
2. A root cut has precisely one valid row. If every cut is the root
   singleton, then $E=\mathcal C_m$ and $U=\mathcal T$.
3. Empty cuts and fully blocked cuts have ground exteriors and no
   class variables. Deep and mixed cuts use their exact finite
   addresses and blockers. Equal epochs use the same whole tree at
   those captures, without weakening any conjunct.
4. No epoch bound depending only on the cut depths can replace the
   row-dependent threshold for general inputs.

Proof. The first three statements follow directly from validation,
the filling supplier and the fixed-epoch formula. For the fourth,
take two empty cuts and full rows $\alpha,T_j$. Their unique lag
is $j$, by injectivity and distinctness of the atomic orbit. Both
cut depths are zero while $j$ is arbitrary. The literal second row
has grown; its finite exterior is part of the input to (NUE.5).
$\square$

**Proposition 6.3 (retained cross-epoch links defeat this cap).** The
coordinatewise cap theorem does not extend merely by adding equality
links between hidden subtrees at independently varying epochs. This
failure already occurs when the original source is uniquely fixed.

Proof. Use three rows. The first has empty cut and full tree
$t=\langle\beta,\alpha\rangle$. Each later cut is $\{L,R\}$,
with a two-hole exterior and two distinct classes. These later rows
hold for every epoch, since

$$
\rho^n t=\langle T_{n+1},T_n\rangle.
\tag{NUE.22}
$$

For these row-only data, (NUE.5) gives thresholds $4,2,2$ and hence
$B=4$. Add the extra retained relation

$$
(\rho^{n_1}t)|_L=(\rho^{n_2}t)|_R.
\tag{NUE.23}
$$

Both endpoints are reached at every epoch. By (NUE.22), the exact
extended fiber is
$\{(0,n,n+1):n\ge0\}$. For every $n\ge4$, capping such a
tuple gives $(0,4,4)$, whose linked values are $T_5$ and $T_4$,
which differ. In fact any common finite cap fails on a sufficiently
late tuple of this form. The initial full row fixes $t$, so changing
an existential witness cannot rescue that capped tuple either.

Relation (NUE.23) is not a partition bit within one capture. Capping
changes the two epochs by different amounts; injectivity reflects
equality after the same number of updates, not after unrelated
numbers. This refutes this reduction for the enlarged language,
not the decidability of that language. The displayed extended
fiber itself has a simple linear description. $\square$

## 7. Representation, decision, observation and retained memory

**Definition 7.1 (separate mathematical resource quantities).** The
input size includes every literal exterior constructor and leaf,
every hole and cut address with its full word length, and a complete
partition encoding. A partition can be encoded by one class number
per hole; its semantics still includes all different-class
disequalities. Expanding (NUE.4) explicitly adds
$\sum_i\binom{|\mathcal B_i|}{2}$ such disequalities.

The support output $(B,K)$, its local decision workspace, any retained
input rows, any stored finite original witnesses, and the expanded
trees at requested epochs are different quantities. An authentic
given epoch count is additional evidence, separate from a compatible
count inferred from (NUE.13). A literal query address is ordinary
data; it is not a compressed pointer to an unknown subtree.

**Proposition 7.2 (finite representation and decision costs at their
stated interfaces).** A tuple-list encoding of $K$ uses
$O(|K|m\log(B+1))$ bits for its entries, in addition to the encoding
of $B$, the input and optional witnesses. The exhaustive construction
uses the number of fixed-epoch feasibility calls in (NUE.11).
Membership after construction requires only chronology, capping and
finite-table membership. For one fixed nonempty input, selecting one
finite original per accepted region gives an effective bound on the
sizes of these selected originals, uniform over all its feasible epochs.
This is not a bound on all compatible originals. No polynomial
total-time bound or input-independent witness bound is asserted.

Proof. Every coordinate of a representative lies in $0,\ldots,B$.
The bit count and call count follow from their respective finite
encodings and Theorem 3.3. A query tuple can be capped by comparison
with $B$; this computation depends on its integer representation
length, not on physically executing its count. NSF's calls each
terminate, but their work and witness sizes are separate from how
many calls are made. The maximum size of the finitely many returned
$t_{\mathbf c}$ is the stated bound on selected originals. Root-only
rows still admit originals of every finite size. Even a compact atomic
index can require a large literal tree: with $F_0=0,F_1=1$, $T_r$
has $F_{r+1}$ leaves
and $2F_{r+1}-1$ nodes. Thus an arithmetic representation is not
a unit-cost materialized source. $\square$

**Assumption 7.3 (when a semantic input describes actual captures).**
For an observational interpretation, the rows must actually be
acquired on the stipulated same original-root register, at coherent
captures of its pure-$\rho$ history. Ordinary materialized
$\mathsf{Read}(p)$ returns only
$\alpha,\beta,\mathsf{branch},\mathsf{absent}$. There is no
whole-tree, subtree-equality, boundary-profile or epoch port.

The paid producer [ARH, Proposition 2.1][ARH] is available under
its exact public fixed-schedule, authentic-epoch and complete-access
conditions. It acquires finite descriptions by literal traversal
and compares those descriptions locally, retaining and transporting
them until their intended comparisons are made. Raw calls, full
address lengths, comparison work, workspace, retention, transport,
updates and epoch certification remain separately charged. Its
sourcewise finite acquisition cost is not a uniform cost bound.
Its schedule and retained-state hypotheses are not silently replaced
by unknown epochs or adaptive selection.

Theorems 3.3 and 4.1 are offline consumers of supplied finite
mathematical records. They supply no new producer, no free observation
port and no concurrent snapshot guarantee. If concurrent reads are
used, the coherent-capture conditions must be established at that
interface; [Concurrent Native Cut Acquisition, Definitions 1.3--1.4][CNA]
explicitly distinguish such conditions from a sequence of atomic
individual reads. Source-dependent acquisition control or undiscarded
auxiliary state changes the observation fiber unless included in the
retained input. None of these physical premises is inferred by a
successful consistency decision.

## 8. Supplier boundaries and the remaining relational questions

**Definition 8.1 (scope of the increment).** The following correspondence
fixes the mathematical suppliers and the additional inference.

| Supplier | Exact role and boundary |
| --- | --- |
| [NAR, Definitions 1.1--1.2, Propositions 10.3 and 12.6][NAR] | Native complete records and the exact unknown-epoch target. Overlap-clock consistency supplies necessary component differences; it is not joint feasibility. |
| [NSF, Definition 1.1, Lemma 5.1 and Theorem 5.2][NSF] | Total fixed-numeral native feasibility, arbitrary complete-row tests, Boolean disequalities and finite witnesses. Every actual call in Theorems 3.3 and 4.1 has supplied numeral epochs. |
| [NSF, Lemma 9.2][NSF] | All-source deep-prefix saturation, reached transport, injectivity and distinct iterates. Theorem 2.2 applies these to equality with one fixed proposed row. |
| [ABC, Theorems 2.2--2.3][ABC] | Existing all-native normal coordinates, exact expansion and rank translation. No replacement normal algebra or new variable-power solver is introduced. |
| [ARH, Theorem 5.2][ARH] | Earlier eventual index truth on a source fiber forced to the atomic orbit. Its atomic restriction is preserved; it is not asserted to quantify arbitrary fixed originals. |
| [NAR, Theorem 14.8][NAR]; [NARC, Theorem 1.2][NARC] | Sharper interval and resource results on their fixed bounded-age atomic-slot families. No such family restriction is imposed on (NUE.3). |
| [NIC, Definition 1.2][NIC]; [NIS, Section 11][NIS] | Variable atomic $T_{n+c}$ and fixed residual powers have their stated grammar. Arbitrary quantified $\rho^n(z)$ does not become admissible there through a renamed parameter. |
| [Intrinsic coordinates][INTR]; [Boundary IV, Theorems 113.4--113.5][BOUNDARY] | Full-tree primitive ancestry, invariant boundary measure and scale recovery on the attained image. They do not supply missing acquisition or uniquely select a source from arbitrary incomplete rows. |

The source-level correspondence is also explicit. In the native
formal carrier $\alpha$ is `FreeMagma.of true`, $\beta$ is
`FreeMagma.of false`, and $\rho$ is `substitution`. The public and
private declarations below identify the reused interfaces; their
corresponding Scribes describe the same mathematical boundaries.

| Declaration source and corresponding Scribe | Interface |
| --- | --- |
| [NativeCutFibers][CUT], [Scribe][CUT-S] | `legal_values_row`, `rowFiberEquiv`, private `recover_fill` and `fill_injective`: exact complete old-row filling, with unrestricted finite class values and all class disequalities. |
| [ActualCutPartitionDecoder][ROW], [Scribe][ROW-S] | `literalRecord`, `canonicalRow_record_iff`, `nameExterior_correct`, private `eraseClasses_literal`: addressed exterior plus full partition, including zero holes. |
| [NativeDepthPatterns][DEPTH], [Scribe][DEPTH-S] | `original_present_transport`, `depthEquiv`, private decomposition inverses: actual reached transport and exact finite-prefix decomposition. `History` stores supplied natural epochs. |
| [NativeHistoryCells][HISTORY], [Scribe][HISTORY-S] | `cell_feasibility_exact`, `historyCellEquiv`, private `syntax_iff_ground`: whole legal fixed-history cells, not an unknown-epoch decision. |
| [NativePredecessorRowRecovery][BACK], [Scribe][BACK-S] | `native_predecessor_row_recovery`, private `delta_sigma`: one actual update with supplied old occurrence support, not an unbounded-epoch gluing algorithm. |
| [IntrinsicSubstitutionCoordinates][INTR], [Scribe][INTR-S] | `intrinsic_coordinates`, private `legal_iff`, `root_primitive`, `substitution_injective`: full-source ancestry and injectivity, with no record-acquisition assertion. |

These are source correspondences, not fresh compilation evidence.
The substantive additional conclusions are the sourcewise row
threshold (NUE.6), the same-original factorization (NUE.10), its
effective support and uniqueness consumers, and the native joint
obstructions with their stated language boundary.

**Open problem 8.2 (richer retained relations).** Consider finite terms
with the explicit grammar

$$
A::=\alpha\mid\beta\mid z_j\mid\langle A,A\rangle
       \mid\rho^k(A)\mid\rho^{n_i}(A),
\qquad k\in\mathbb N\text{ a supplied numeral}.
\tag{NUE.24}
$$

For a finite Boolean combination of equalities between these terms,
with repeated names shared, all $z_j$ existentially ranging over
$\mathcal T$, and free natural parameters $n_i$ subject to chronology,
give an exact effective parameter projection and finite native witnesses.
No quantified addresses, arbitrary replacement operation, rational
trees or alternating tree quantifiers are included in this question.
A solution must prove both directions at the identical parameter tuple.
Proposition 6.3 shows why the present
sourcewise coordinate cap is insufficient. It does not show that
such a richer solver is impossible. A parameter-uniform extension
of the fixed-power witness reduction is a possible separate route;
its uniformity and admissible-language proof are not supplied here.

**Open problem 8.3 (operational mutual recovery).** Determine which
actually acquirable and retainable interfaces allow the semantic
relation (NUE.10) to yield exact internal recovery with optimal
resources. The questions include coherent concurrent acquisition,
unbounded physical address choices, workspace and retained-memory
tradeoffs, and recovery of boundary data when the whole original
is not determined. Relative update counts do not by themselves
recover physical durations. A finite description of compatible
histories is not a universal minimal relational structure, a proof
of physical provenance, or a completion of these further tasks.

## 9. Mathematical literature and transfer conditions

**References 9.1 (primary results used for comparison).** The
arithmetic regions here are constructed explicitly in (NUE.12);
their native correspondence is proved before they are classified
arithmetically. The following established results delimit related
formulations. None is invoked with an enlarged language or changed
quantifier order.

| Primary source | Exact correspondence and limitation |
| --- | --- |
| Ginsburg and Spanier, *Semigroups, Presburger Formulas, and Languages*, Pacific Journal of Mathematics 16(2), 285--296, Theorems 1.2--1.3, [publisher text][GS] | `literature-attested`: Presburger sentence decidability and effective equivalence with semilinear subsets of natural integer lattices. Equation (NUE.12) already gives the constants and generators directly; this result does not prove native row stabilization or remove native variables. |
| Marshall, Meadows and Narendran, *On Unification Modulo One-Sided Distributivity: Algorithms, Variants and Asymmetry*, arXiv:1503.06687v2, Sections 4--5, Theorems 4.4 and 5.8, [primary text][MMN] | `literature-attested`: unification for the stated typed single-homomorphism theory, with a subterm-collapse-free cycle argument. The native constant laws are extra: $\rho(x)=\langle x,\alpha\rangle$ has the finite solution $x=\beta$. Thus a raw free-theory occurs rejection cannot be transferred to this interpreted operation. |
| Cerna, *Schematic Unification*, arXiv:2306.09152v7, Definitions 2--6 and the stated infinity-stability condition, [primary text][CERNA] | `literature-attested`: iterated indexed-variable substitution schemas and a sound terminating algorithm for uniform schematic problems, with completeness under infinity-stability. Its question asks whether every schematic instance is unifiable. Here finitely many unknown epochs and one finite ground original are existentially shared; no quantifier-preserving reduction is inferred. |
| Durand, *Decidability of the HD0L ultimate periodicity problem*, arXiv:1111.3268v3, Section 1.1 and Theorem 1, [primary text][DURAND] | `literature-attested`: ultimate periodicity of the specified morphic-word system with given alphabets, morphisms and seed word. Native trees can be serialized faithfully in prefix notation using a pair symbol $p$, with $a\mapsto b$, $b\mapsto pba$, $p\mapsto p$. This intertwines the operations, but the seed here is unknown and multiple existential epochs share it; word-limit periodicity does not supply the required finite-tree joint decision. |
| Atserias and Kolaitis, *Consistency, Acyclicity, and Positive Semirings*, arXiv:2009.09488v1, Sections 3--4, Theorems 3--4, [primary text][AK] | `literature-attested`: local-to-global consistency for $K$-relations over acyclic attribute hypergraphs, with marginal-consistency hypotheses. Nonempty pairwise native-history intersections are weaker than those hypotheses. A tree-shaped address space or a connected clock graph does not establish the required relation-schema acyclicity. Proposition 5.1 gives the direct native obstruction. |

The native deductions in Sections 2--7 are `repo-derived`. The
normal coordinates, fixed-epoch decision, finite-tree methods,
Presburger/semilinear vocabulary and local-to-global distinction
are reused mathematical ingredients. No worldwide priority,
general undecidability, implemented-solver, or low-cost observation
claim is attached to their application here.

[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[NARC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[NIS]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_SATURATION.md
[BOUNDARY]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IV.md
[CNA]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md
[CUT]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.lean
[ROW]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.lean
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[HISTORY]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.lean
[BACK]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.lean
[INTR]: ../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean
[CUT-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers.scribe.cs
[ROW-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCutPartitionDecoder.scribe.cs
[DEPTH-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.scribe.cs
[HISTORY-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeHistoryCells.scribe.cs
[BACK-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.scribe.cs
[INTR-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs
[GS]: https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf
[MMN]: https://arxiv.org/html/1503.06687v2
[CERNA]: https://arxiv.org/html/2306.09152v7
[DURAND]: https://arxiv.org/html/1111.3268v3
[AK]: https://arxiv.org/html/2009.09488v1

## 追加锚（本行以下为增补区）
