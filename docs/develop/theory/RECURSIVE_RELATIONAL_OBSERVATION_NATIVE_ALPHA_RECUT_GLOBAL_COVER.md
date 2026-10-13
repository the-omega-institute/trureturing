# Native alpha recut global covers: difference gaps and joint balance

## 1. The complete native cover domain

**Assumption 1.1 (source, acquired label and universal recovery).**
Use [Native alpha recut memory continuation, Assumptions 5.1 and 9.1,
Definition 13.1][NARC], with public $q\in\{18,19\}$ and
$\lambda\in\{0,1\}$. The original sources are all

$$
X_{a,b}=\langle T_a,T_{q+b}\rangle,
\qquad (a,b)\in\Omega_q:=\{0,\ldots,q-1\}^2,
\qquad T_n=\rho^n\alpha.
\tag{NAGC.1.1}
$$

The source algebra, homomorphic substitution, literal constructor port
and complete cut row are [NAR, Definitions 1.1--1.2][NAR]. In particular
$\rho\alpha=\beta$, $\rho\beta=\langle\beta,\alpha\rangle$,
and $T_{n+2}=\langle T_{n+1},T_n\rangle$. Original offsets remain
$0,q$. The encoder computes one deterministic label $e(a,b)$ from
the genuinely acquired original empty-cut row, before the future cut
and lag are chosen. Exactly $q$ labels are attained. The original
row, parsed coordinates and every other source-bearing field are
discarded; a surviving source-dependent selection counts as part of
the label. The public encoder table is common to all sources.

The same original continues by its own $\ell$ substitutions, with
$\ell\ge\lambda$. The later entire row is genuinely acquired at
the selected cut $\varnothing$, $\{L\}$ or $\{R\}$, and the
current tree remains stationary during all subsequent Reads. One
deterministic service must return that original's $\ell$ for every
original, every permitted cut and every permitted lag, using at most
two chronological native Reads. Each request is a fully materialized
finite original-root word; repeated requests and the empty word are
paid again. Local computation may depend on the acquired entry and
earlier actual replies and must terminate on every promised input.
No fixed finite controller, address cap or workspace cap is assumed.

The original semantic correspondence is [NAR, Assumptions 11.1,
13.1 and 16.1, Reuse 16.2][NAR]. The acquired-literal clock computes
$a,b$ before discard and the visible normalized clock $z$ afterwards;
it supplies no hidden age. For an entire class $C$, [NARC, Theorem
5.2][NARC] gives exactly

$$
\begin{array}{c|c|c|c}
\text{visible slot}&\text{complete origin fiber}&\text{hidden age}
 &\text{required lag}\\ \hline
R&\{(a,b)\in C:b\le z-\lambda\}&z+a-b&z-b\\
L&\{(a,b)\in C:a\le z-\lambda\}&q+z-a+b&z-a.
\end{array}
\tag{NAGC.1.2}
$$

Equality of entries includes the full literal exterior, reached hole
and complete singleton partition. Every index in these sets denotes
its own fixed-original history. The native $E/P/S$ law, including
the absence of $P_1$, is [AOF, Definition 8.2][AOF] and [NARC,
Definition 5.3][NARC]. Root and visible-slot replies are constant on
each complete entry; hidden-slot replies obey that law. Subsequent
supports retain all original indices compatible with the actual
transcript. Acquisition, discard and same-original continuation are
premises, not conclusions authenticated by the returned integer.

**Definition 1.2 (inherited families and one simultaneous cover).**
Write $d(a,b)=a-b$. Reuse the complete families of [NARC, Definition
14.1 and Theorem 15.2][NARC] by setting

$$
\mathcal F_{q,t}^{\lambda}=
\begin{cases}
\mathcal P_t^+,&q=19,\ \lambda=1,\\
\mathcal P_t^0,&q=19,\ \lambda=0,\\
\mathcal A_t^{\lambda},&q=18,
\end{cases}
\qquad 0\le t<q.
\tag{NAGC.1.3}
$$

Throughout, a cover means one choice $C_t\in\mathcal F_{q,t}^{\lambda}$
for each $t$, with pairwise disjoint classes and union $\Omega_q$.
Each class has its unique diagonal anchor $(t,t)$ and $d$ is
injective on it. The label $t$ is just the inherited bijective
relabeling by this anchor. [NARC, Theorems 14.2 and 15.2][NARC]
already identify these covers with the respective unrestricted
two-read encoder problems. On the empty cut, the two normalized acquired
current clocks give $d$; its injectivity in the known class fixes the original
and lag without fresh Reads, as in [NARC §§5, 9 and 12][NARC].

At nineteen labels every class has nineteen points. Its increasing-$d$
list has six consecutive pure triples, three $AAA$ and three $BBB$,
where $A$ increases $a$ and $B$ decreases $b$. Every middle edge is
unit. All twenty macro words, all initial points and all positive
integer outer lengths are permitted, subject only to square membership
and the specified anchor.
The nonnegative family imposes precisely [NARC, Theorem 13.4][NARC]'s
additional exclusion of an initial point with $a=0$ followed by a
unit first $B$ edge. These are inherited local results.

At eighteen labels the family retains every nonempty $d$-injective
class passing both full origin-indexed $D_2$ reference tests of
[NARC, Theorem 10.2][NARC]. For $\lambda=0$ it also retains the
requirement $D_2$ on every complete state

$$
\bigl((z+a-b,b)\bigr)_{(a,b)\in C,\ b\le z}
\quad\text{whenever }(0,z)\in C,\quad 0\le z<18.
\tag{NAGC.1.4}
$$

The two axis-monotone defect-one cases still require their nine-run
target tests. Fused classes can change both coordinates, revisit a
coordinate value and fail axis monotonicity. Saturated classes and
all higher-defect mixtures remain admitted by the same exact tests.
The saturated first-step exclusion is not substituted for (NAGC.1.4).
No anchor belt or monotone-deletion restriction is imposed; [NARC,
Propositions 15.3 and 15.4][NARC] rule out those local transfers.

**Definition 1.3 (class size and defect).** Put

$$
m_t=|C_t|,\qquad \delta_t=19-m_t.
\tag{NAGC.1.5}
$$

The inherited bounds and defect accounting [NARC, Theorems 9.2,
13.2 and 15.1][NARC] give $1\le m_t\le19$, $\delta_t\ge0$ and
$\sum_t\delta_t=q(19-q)$. Thus every defect is zero at $q=19$,
whereas their sum is eighteen at $q=18$. In the latter case the
number of saturated classes equals
$\sum_{\delta_t\ge2}(\delta_t-1)$. No particular allocation of
these defects is fixed below.

## 2. Integer spans, missing memberships and endpoints

**Definition 2.1 (span statistics).** For every class set

$$
\begin{aligned}
D_t&=\{d(a,b):(a,b)\in C_t\},&
L_t&=\min D_t,&U_t&=\max D_t,\\
g_t&=U_t-L_t+1-m_t,&G&=\sum_t g_t.
\end{aligned}
\tag{NAGC.2.1}
$$

These extrema exist because $(t,t)\in C_t$, and
$-(q-1)\le L_t\le0\le U_t\le q-1$. Difference injectivity
gives $|D_t|=m_t$, so $g_t$ counts the missing integers of
$[L_t,U_t]\cap\mathbb Z$. Define, for every integer $j$,

$$
\begin{aligned}
h_j&=\#\{t:L_t\le j\le U_t,\ j\notin D_t\},\\
\nu_j&=\#\{t:L_t\le j\le U_t\},\\
A_j&=\#\{t:L_t=j\},&B_j&=\#\{t:U_t=j\}.
\end{aligned}
\tag{NAGC.2.2}
$$

All these counts vanish outside the possible spans. A missing
membership $(t,j)$ is not an uncovered source cell: every cell of
the square belongs to a class. Both $g_t$ and $h_j$ retain class
multiplicity, and $G$ is a combinatorial gap count, not a resource
charge on a decoder.

**Theorem 2.2 (complete span and endpoint balance).** Every cover of
Definition 1.2, under either lag convention, satisfies

$$
\begin{aligned}
\nu_j&=q-|j|+h_j && (|j|<q),\\
h_0&=h_{-(q-1)}=h_{q-1}=0,&
0&\le h_j\le |j| &&(|j|<q),\\
G&=\sum_{j\in\mathbb Z}h_j,\\
A_j&=1+h_j-h_{j-1}&& (-(q-1)\le j\le0),\\
B_j&=1+h_j-h_{j+1}&& (0\le j\le q-1),\\
U_t-L_t&=18-\delta_t+g_t,\\
\sum_t(U_t-L_t)&=q(q-1)+G.
\end{aligned}
\tag{NAGC.2.3}
$$

In particular the last total is $306+G$ at eighteen labels and
$342+G$ at nineteen labels. The endpoint equations include the
degenerate endpoint zero. Equivalently, for $1\le k<q$,

$$
\#\{t:U_t<k\}=k-h_k,\qquad
\#\{t:-L_t<k\}=k-h_{-k}.
\tag{NAGC.2.4}
$$

**Proof.** The band $d=j$ has exactly $q-|j|$ cells when $|j|<q$.
Complete disjoint coverage puts these in $q-|j|$ different classes,
since one class cannot contain two equal differences. A span covering
$j$ either supplies its one occupied difference or omits that integer.
Counting these alternatives gives the first equation. At zero every
class contains its anchor. At either extreme, a span reaches the
extreme integer only if that integer is its occupied endpoint. Hence
the three stated $h$ values vanish. Since $\nu_j\le q$, the first
equation also gives $h_j\le|j|$. Counting the pairs $(t,j)$ with
$j\in[L_t,U_t]\setminus D_t$ in the two orders proves the equation
for $G$.

For $j\le0$, every $U_t\ge0$ implies that no interval ends before
$j$. Therefore $\nu_j-\nu_{j-1}=A_j$. At the lowest index use
$\nu_{-q}=h_{-q}=0$; throughout the specified range the occupied
band count increases by one. This proves the equation for $A_j$.
For $j\ge0$, every $L_t\le0$ implies that no interval begins after
$j$, and $\nu_j-\nu_{j+1}=B_j$. At the highest index use
$\nu_q=h_q=0$. The occupied count decreases by one, giving the
equation for $B_j$. In particular
$A_0=1-h_{-1}$ and $B_0=1-h_1$, with singleton spans counted by
both endpoint statistics when they occur.

For positive $k$, a span contains $k$ exactly when $U_t\ge k$.
Subtracting $\nu_k=q-k+h_k$ from $q$ gives the first identity
of (NAGC.2.4). Apply the same argument to $-k$ for the second.
The class-size definition gives $U_t-L_t=m_t-1+g_t$.
Summing it uses $\sum_t m_t=q^2$ and exactly $q$ classes, yielding
$q^2-q+G$. All arguments use occupied differences rather than
coordinate step signs. They therefore include nonmonotone fused
classes and every allowed defect allocation. $\square$

## 3. Signed ranks and the defect moment

**Definition 3.1 (signed rank excess).** List the positive differences
of $C_t$ and the absolute values of its negative differences as

$$
1\le x^+_{t,1}<\cdots<x^+_{t,p_t},\qquad
1\le x^-_{t,1}<\cdots<x^-_{t,n_t}.
\tag{NAGC.3.1}
$$

An empty list has length zero. Put $u_t=U_t$ and $v_t=-L_t$;
these are respectively zero if the positive or negative list is empty.
Define

$$
\begin{aligned}
g_t^+&=u_t-p_t,&g_t^-&=v_t-n_t,&
G^+&=\sum_tg_t^+,&G^-&=\sum_tg_t^-,\\
H_t^+&=\sum_{i=1}^{p_t}(x^+_{t,i}-i),&
H_t^-&=\sum_{i=1}^{n_t}(x^-_{t,i}-i),&
H^+&=\sum_tH_t^+,&H^-&=\sum_tH_t^-.
\end{aligned}
\tag{NAGC.3.2}
$$

Empty sums are zero. The anchor is the sole difference-zero point,
so $p_t+n_t=m_t-1$. Consequently $g_t=g_t^++g_t^-$ and
$G=G^++G^-$. In terms of Definition 2.1,
$G^+=\sum_{k=1}^{q-1}h_k$ and
$G^-=\sum_{k=1}^{q-1}h_{-k}$.

**Theorem 3.2 (joint rank and defect identities).** For every cover
of Definition 1.2 set $S_q=q(q^2-1)/6$. Then

$$
\begin{aligned}
\sum_t p_t&=\sum_t n_t=\frac{q(q-1)}2,\\
H^+&=S_q-\sum_t\frac{p_t(p_t+1)}2,&
H^-&=S_q-\sum_t\frac{n_t(n_t+1)}2,\\
2(H^+-H^-)&=\sum_t\delta_t(p_t-n_t),\\
H_t^+&\ge g_t^+\ge0,&H_t^-&\ge g_t^-\ge0.
\end{aligned}
\tag{NAGC.3.3}
$$

At $q=19$ the signed moments are equal. At $q=18$ their exact
imbalance is coupled to the whole defect allocation by the third
equation, with $\sum_t\delta_t=18$. If no eighteen-label class
is saturated, the inherited defect theorem forces every
$\delta_t=1$, and these moments are again equal. No common-size
hypothesis is needed for the general identity.

**Proof.** Counting occupied cells above and below the diagonal gives
the first equality. Weight each positive band by its difference:

$$
\sum_t\sum_{i=1}^{p_t}x^+_{t,i}
=\sum_{k=1}^{q-1}k(q-k)
=\frac{q(q^2-1)}6.
\tag{NAGC.3.4}
$$

The last equality follows by substituting
$\sum_{k=1}^{q-1}k=q(q-1)/2$ and
$\sum_{k=1}^{q-1}k^2=q(q-1)(2q-1)/6$ into
$q\sum k-\sum k^2$. Negative bands have the same absolute
weighted total. Subtracting the respective sums of ranks $i$ proves
both moment formulas. Their difference is

$$
\begin{aligned}
2(H^+-H^-)
 &=-\sum_t\bigl(p_t(p_t+1)-n_t(n_t+1)\bigr)\\
 &=-\sum_t(p_t-n_t)(p_t+n_t+1)\\
 &=-\sum_t(19-\delta_t)(p_t-n_t)\\
 &=\sum_t\delta_t(p_t-n_t),
\end{aligned}
\tag{NAGC.3.5}
$$

because $p_t+n_t+1=m_t$ and $\sum_t(p_t-n_t)=0$.

For a nonempty signed list, its $i$th value is at least $i$.
Every summand defining its $H_t$ is nonnegative, and its last
summand is its endpoint minus its length, exactly $g_t$ for that
sign. An empty list has endpoint, gap count and moment all zero.
This proves the inequalities without excluding a class with only
one sign, or even a singleton anchor. More precisely, $x_i-i$
counts omitted positive integers below $x_i$; hence the signed
moment counts each missing rank once for each occupied rank above
it. Every omitted rank in the span has the endpoint above it.
Thus $H_t^\pm=0$ holds exactly when $g_t^\pm=0$, including
the empty case, although their positive values need not agree.

At nineteen labels all defects vanish. At eighteen labels the
general equation uses the inherited total defect; if every defect
is one, its right side is $\sum_t(p_t-n_t)=0$. None of these
calculations constrains a double-coordinate edge or replaces a
complete zero-containing state by a substate. $\square$

## 4. The corner classes force global gaps at nineteen labels

**Definition 4.1 (saturated path data and corner classes).** In this
section $q=19$. For $C_t$ write its increasing-$d$ vertices as
$z_0,\ldots,z_{18}$ and its positive pure edge lengths as
$\ell_1,\ldots,\ell_{18}$. Reuse [NARC, Theorem 13.3][NARC]:
the unit middle positions are $2,5,8,11,14,17$, with nine $A$
and nine $B$ edges in arbitrary permitted macro order. Telescoping
along that supplied path gives

$$
g_t=\sum_{i=1}^{18}(\ell_i-1)
=\bigl(\max_{C_t}a-\min_{C_t}a\bigr)
 +\bigl(\max_{C_t}b-\min_{C_t}b\bigr)-18.
\tag{NAGC.4.1}
$$

Let $N$ be the unique class containing $(0,18)$ and $P$ the unique
class containing $(18,0)$. Use the same class statistics for these
names, for example $D_N,L_N,U_N,g_N$ and $D_P,L_P,U_P,g_P$.
These names may denote the same class. The two distinct gates
$m_+,m_-\in\{2,\ldots,16\}$ and their adjacent-band ownership
are exactly [NARC, Theorem 14.3, (NARC.14.2)][NARC]. In particular
$C_{m_+}$ is the unique class missing difference $1$, and
$C_{m_-}$ the unique class missing difference $-1$; a missing
difference need not lie inside that class's span.

**Lemma 4.2 (corner endpoints and small corner budgets).** In every
nineteen-label cover:

1. $L_N=-18$, $U_N=g_N$, $U_P=18$, and $L_P=-g_P$.
   If $N=P$, then $g_N=18$.
2. A class ending at difference zero must be the all-unit class
   $N=C_9$. A class starting at difference zero must be the all-unit
   class $P=C_9$. Thus $N,P$ cannot both have gap count zero, and

$$
h_1=\begin{cases}0,&g_N=0,\\1,&g_N>0,\end{cases}
\qquad
h_{-1}=\begin{cases}0,&g_P=0,\\1,&g_P>0.\end{cases}
\tag{NAGC.4.2}
$$

3. A corner class with gap count one contains both differences
   $-1$ and $1$. A corner class with gap count two cannot omit
   both of them.
4. If $P$ is all-unit, then $N\ne P$, $g_N\ge3$, and $g_N=3$
   implies $D_N\cap\mathbb Z_{>0}=\{1,2,3\}$.
   If $N$ is all-unit, then $g_P\ge3$, and $g_P=3$ implies
   $D_P\cap\mathbb Z_{<0}=\{-1,-2,-3\}$.

**Proof.** A corner difference is extremal in the square and therefore
an endpoint of its class. Since $m=19$, Definition 2.1 gives the
four endpoint identities and the same-class value eighteen.

Suppose a class ends at $(t,t)$. Its nine positive $A$ lengths
and nonnegative starting first coordinate give $t\ge9$. Its nine
positive $B$ lengths and starting second coordinate at most eighteen
give $t\le9$. Equality forces start $(0,18)$ and every edge
unit. Conversely $g_N=0$ makes $U_N=0$, so it is exactly this
case. If a class starts at $(t,t)$, the terminal bounds instead
give $t\le9$ from its $A$ changes and $t\ge9$ from its $B$
changes. Its endpoint is $(18,0)$ and every edge is unit. The
converse is again the corner endpoint formula. Both unit cases
would have anchor nine. If they coincided their gap count would
be eighteen, not zero, and if they were distinct they would share
the anchor. Neither is possible. Finally Theorem 2.2 gives
$B_0=1-h_1$ and $A_0=1-h_{-1}$. The just established unique
possibilities for these endpoints give (NAGC.4.2).

For the small-budget claim consider $N$. If $g_N=1$, its span
is $[-18,1]$ with exactly one missing integer. Difference $1$
is its endpoint. If $-1$ were the missing integer, its last three
vertices would have differences $-2,0,1$. Edge seventeen would
then have length two, contradicting its unit middle position.
If $g_N=2$ and both $-1,1$ were missing, these would be its only
omissions in $[-18,2]$. Its last three differences would be
$-2,0,2$, giving the same contradiction at edge seventeen.

For the assertions concerning $P$, use coordinate complementation
$(a,b)\mapsto(18-a,18-b)$ and reverse each vertex list. This
bijection sends $d$ to $-d$, exchanges the two corners, relabels
anchor $t$ by $18-t$, preserves every edge length and every pure
triple, and preserves the unit middle positions. It preserves a
disjoint geometric saturated cover. It therefore transfers the
small-budget statements just proved. This is a transformation of
the positive geometric cover domain, not a claim that the
nonnegative native first-step test is invariant under it.

For part 4 suppose $P$ is all-unit. It is $C_9$ and has no
negative differences, so the unique negative-band missing label
is $m_-=9$. The other corner has a different anchor $t\ne9$
and $g_N>0$. Put $r=\#(D_N\cap\mathbb Z_{>0})$; its positive
endpoint $U_N=g_N$ gives $1\le r\le g_N$. Because only $C_9$
misses difference $-1$, $N$ contains that difference immediately
before its anchor in $d$ order. The gate formula locates it as

$$
\begin{cases}
(t,t+1),&t<9,\\
(t-1,t),&t>9.
\end{cases}
\tag{NAGC.4.3}
$$

If $r=1$ or $2$, the anchor has vertex index $18-r$, namely
seventeen or sixteen. The edge entering it and all remaining edges
then belong to the last pure triple, with the same direction $X$.
If $X=A$, all nine $B$ changes have already occurred at the
anchor. Starting from $b=18$ gives $t\le9$, and hence $t<9$.
But (NAGC.4.3) requires a $B$ edge into that anchor, contrary to
$X=A$. If $X=B$, all nine $A$ changes have already occurred;
starting from $a=0$ gives $t\ge9$, and hence $t>9$. Formula
(NAGC.4.3) requires an $A$ edge into the anchor, another
contradiction. Thus $r\ge3$ with no assumption on the other
classes' budgets. Consequently $g_N\ge3$, and at equality its
three positive differences must be precisely $1,2,3$.
The same coordinate complementation transfers this geometric
statement to the case that $N$ is all-unit. $\square$

**Lemma 4.3 (the complete zero-origin contribution).** In a
nineteen-label cover under $\lambda=0$, the class $C_0$ has
$g_0\ge1$. If $g_0=1$, its only missing difference is $-9$.
If $C_0$ omits both $-1$ and $1$, then $g_0\ge3$.
If $C_0$ contains either extreme corner, then $g_0\ge9$.

**Proof.** [NARC, Theorem 14.3][NARC] forces $C_0$ to be the
$B^9A^9$ path with minimum corner $(0,0)$. Its first point has
first coordinate zero. The exact saturated zero-origin theorem
[NARC, Theorem 13.4][NARC] therefore makes its first $B$ length
at least two. Formula (NAGC.4.1) gives $g_0\ge1$.

If $g_0=1$, the first length is two and every other length is one.
The path starts at $(0,10)$, follows the $b$ values
$10,8,7,\ldots,0$, and then the $a$ values $1,\ldots,9$.
Its difference span is $[-10,9]$ and its sole omitted integer is
$-9$. In particular it omits neither adjacent difference.

On this L path, omitting $-1$ requires its final $B$ length to
be at least two, and omitting $1$ requires its first $A$ length
to be at least two. These are distinct from each other and from
the first $B$ edge, since there are nine $B$ edges. Omitting
both therefore supplies three separate units of excess.

If $C_0$ contains $(0,18)$, its $B$ span is eighteen, while its
nine $A$ changes have total length at least nine. Formula
(NAGC.4.1) then gives $g_0\ge18+9-18=9$. If it contains
$(18,0)$, its $A$ span is eighteen and the analogous argument
uses the nine $B$ changes. This proof uses the zero theorem only
on a saturated class and its inherited complete-fiber contract.
$\square$

**Theorem 4.4 (unrestricted four-gap and five-gap necessities).**
Every nineteen-label cover of Definition 1.2 satisfies

$$
G\ge4\quad(\lambda=1),\qquad
G\ge5\quad(\lambda=0).
\tag{NAGC.4.4}
$$

For both conventions $G^+\ge1$, $G^-\ge1$ and $H^+=H^-$.
Their common moment is at least two for positive lags and at
least three for nonnegative lags. The corresponding total spans
are at least $346$ and $347$. These are necessary bounds;
attainment of either gap bound is not asserted.

**Proof, positive lags.** Every nonnegative-lag cover belongs to
the positive geometric domain as well. First prove $G\ge4$
there. If $N=P$, Lemma 4.2 gives $G\ge18$. Otherwise the
corners are distinct and cannot both be unit. Suppose $G\le3$.

If both corners have positive gaps, (NAGC.4.2) requires one
omitted membership at each of $-1,1$. Their positive integer
budgets are either $1+1$ or $1+2$ in some order. In the first
case neither corner omits either adjacent difference by Lemma
4.2. Supplying the two missing memberships elsewhere needs at
least two additional gap units, although at most one remains.
In the second case all gap units are already assigned to the
corners. The gap-one corner omits neither adjacent difference,
and the gap-two corner cannot omit both. Both allocations fail.

If $P$ is unit, Lemma 4.2 forces $g_N\ge3$. Under $G\le3$
it is exactly three, all other classes have gap zero, and $N$
contains $1,2,3$. Thus no class omits $1$ inside its span,
contradicting $h_1=1$ from (NAGC.4.2). If $N$ is unit, the
same lemma gives $g_P=3$, containing $-1,-2,-3$, and all other
classes have gap zero. This contradicts $h_{-1}=1$. These
cases exhaust the corner possibilities and prove $G\ge4$.

**Proof, nonnegative lags.** Suppose now $\lambda=0$ and
$G\le4$. Lemma 4.3 gives $g_0\ge1$ and makes $C_0$
distinct from both corner classes, since a coincidence would
give $G\ge9$. The case $N=P$ is already impossible at this
budget. If both corners have positive gaps, their combined
budget is at most three, so it is $1+1$ or $1+2$.

For $1+1$, neither corner supplies either required omission
at $-1,1$. If $g_0=1$, it supplies neither by Lemma 4.3, and
at most one gap unit remains in all other classes. If $g_0=2$,
no other gap unit remains and $C_0$ cannot supply both omissions.
Larger $g_0$ violates $G\le4$. For $1+2$, the entire budget
outside the corners is $g_0=1$; it supplies neither adjacent
omission. The gap-two corner cannot supply both, and the
gap-one corner supplies neither. This also fails.

If $P$ is unit, the other corner has gap at least three. Together
with $g_0\ge1$ and $G\le4$, this forces $g_N=3$, $g_0=1$
and all remaining gaps zero. The class $N$ contains difference
$1$, and $C_0$ omits only $-9$, so $h_1=0$, a contradiction.
If $N$ is unit, Lemma 4.2 instead forces $g_P=3$ and its
negative differences $-1,-2,-3$. The same budget forces
$g_0=1$ and leaves no class able to supply $h_{-1}=1$.
Only the geometric lemma is used in this reversed case; the
zero-origin contribution remains the actual $C_0$ of the
original nonnegative cover. Thus no invariance of its native
zero filter is needed. This proves $G\ge5$.

**Proof, signed consequences.** Theorem 3.2 gives $H^+=H^-$.
If $G^+=0$, every positive list has zero gap and hence zero
moment, by its proof. Moment equality forces every negative
list's moment, and hence gap, to vanish as well. That would
give $G=0$, contrary to the lower bound. Exchanging signs
gives the other strict inequality. Finally
$2H^+=H^++H^-\ge G^++G^-=G$, so integrality gives the
claimed common-moment bounds. The total-span equation of
Theorem 2.2 gives $342+4=346$ and $342+5=347$. $\square$

## 5. Adjacent unequal gates force the two entire second bands

**Theorem 5.1 (second-band ownership and the forced anchor triples).**
Let a nineteen-label cover have adjacent unequal gates. Put
$r=\min(m_+,m_-)$, so initially $2\le r\le15$. Then necessarily
$3\le r\le14$, and the whole second bands obey

$$
e(i+2,i)=e(i,i+2)=
\begin{cases}
i,&0\le i<r,\\
i+2,&r\le i\le16.
\end{cases}
\tag{NAGC.5.1}
$$

If $(m_+,m_-)=(r,r+1)$, the class $C_r$ contains four
successive vertices in one $B$ triple of the form

$$
(r,r+1+x),\quad(r,r+1),\quad(r,r),\quad(r,r-y),
\qquad x\ge2,\quad y\ge3,
\tag{NAGC.5.2}
$$

and $C_{r+1}$, writing $v=r+1$, contains

$$
(v,v+x'),\quad(v,v),\quad(v,v-1),\quad(v,v-1-y'),
\qquad x'\ge3,\quad y'\ge2.
\tag{NAGC.5.3}
$$

Both classes have $b$ span at least twelve and gap count at least
three. If $(m_+,m_-)=(r+1,r)$, the corresponding successive
vertices are instead the $A$ triples

$$
\begin{aligned}
C_r:\quad &(r-y,r),\ (r,r),\ (r+1,r),\ (r+1+x,r),\\
C_v:\quad &(v-1-y',v),\ (v-1,v),\ (v,v),\ (v+x',v),
\end{aligned}
\tag{NAGC.5.4}
$$

with the same lower bounds on $x,y,x',y'$. Their $a$ spans
are at least twelve, and their gap counts are again at least three.
These statements hold under either lag convention.

**Proof, exhaustion of the bands.** First take
$(m_+,m_-)=(r,r+1)$ and write $v=r+1$. For $t<r$ the
inherited first-band formulas put
$(t,t+1),(t,t),(t+1,t)$ in $C_t$. Differences $-1,0,1$
are consecutive integers, so these are consecutive vertices of
that class. They give a unit $B$ edge followed by a unit $A$
edge. A change of direction in the six-triple normal form is a
junction of complete triples. The preceding edge is therefore
the unit middle $B$ edge of the incoming triple, and the
following edge is the unit middle $A$ edge of the outgoing
triple. Hence $(t,t+2)$ and $(t+2,t)$ also lie in $C_t$.
The neighboring edges exist because the incoming edge is third
in its triple and the outgoing edge is first in its triple.

For $t>v$, the first-band formulas instead put
$(t-1,t),(t,t),(t,t-1)$ in $C_t$. This is the analogous
unit $A$-to-$B$ junction, forcing $(t-2,t)$ and $(t,t-2)$.
The two ranges are $t=0,\ldots,r-1$ and $t=r+2,\ldots,18$.
In the band $d=2$ they give, respectively,

$$
\{(i+2,i):0\le i<r\},\qquad
\{(i+2,i):r\le i\le16\}.
\tag{NAGC.5.5}
$$

These are disjoint positions and together exhaust the entire
seventeen-cell band. The same calculation with coordinates
exchanged exhausts $d=-2$. All forced cells are in the square
even at the initial extremes $r=2,15$. Disjointness proves
(NAGC.5.1), and in particular neither $C_r$ nor $C_v$ can
meet either second band. This deduction uses a single actual
cover, not two separately chosen band assignments.

**Proof, the first gate triple.** The class $C_r$ misses
difference $1$, and contains the consecutive points
$(r,r+1),(r,r)$ with differences $-1,0$. Their unit $B$
edge cannot be first in its designated triple: the next middle
edge would reach difference $1$. It cannot be third: the
preceding middle edge would force difference $-2$. Therefore
it is the middle edge. If the preceding outer length were one,
its predecessor would have difference $-2$; hence that length
is $x\ge2$. If the following outer length were one or two,
its successor would have difference $1$ or $2$; hence its
length is $y\ge3$. This proves (NAGC.5.2). Its coordinates
give $r-y\ge0$ and $r+1+x\le18$, so $3\le r\le15$.

**Proof, the second gate triple.** The class $C_v$ misses
difference $-1$, and contains the consecutive points
$(v,v),(v,v-1)$ with differences $0,1$. Their unit $B$
edge cannot be first in its triple, because the following
middle edge would reach difference $2$. It cannot be third,
because the preceding middle edge would force difference
$-1$. It is the middle edge. The preceding outer length
cannot be one or two, since its predecessor would have
difference $-1$ or $-2$; thus $x'\ge3$. The following
outer length cannot be one, since that would reach difference
$2$; thus $y'\ge2$. This proves (NAGC.5.3). Its coordinates
give $v+x'\le18$ and $v-1-y'\ge0$, so $v\le15$ and
$v\ge3$, or $2\le r\le14$. Combining the two classes'
necessary bounds yields $3\le r\le14$.

Each displayed triple has length at least six. The other six
$B$ edges have total length at least six, so the whole $b$
span is at least twelve. Its nine $A$ edges contribute at least
nine. Formula (NAGC.4.1) therefore gives $g_r,g_v\ge3$.
No condition was imposed on the positions or lengths of the
remaining triples.

**Proof, reversed gates.** Transpose all cells by
$(a,b)\mapsto(b,a)$ and reverse every ordered vertex list.
This preserves disjoint saturated geometric coverage, keeps
anchor $t$ at $(t,t)$, interchanges the gates and exchanges
$A$ and $B$ lengths. It also preserves each unit middle edge.
The established positive-geometric statement applied to this
cover gives the same symmetric second-band equation, while
transposing and reversing (NAGC.5.2)--(NAGC.5.3) gives
exactly (NAGC.5.4). It supplies the asserted $a$ spans and
gap counts. A nonnegative cover is a member of this positive
geometric domain; this argument does not assert that its
transpose passes the native zero-origin filter. $\square$

**Theorem 5.2 (adjacent-gate gap bounds and four excluded branches).**
In the adjacent-gate case of Theorem 5.1,

$$
\begin{array}{c|c|c|c}
\text{lag convention}&G&H^+=H^-&\sum_t(U_t-L_t)\\ \hline
\lambda=1&\ge6&\ge3&\ge348\\
\lambda=0&\ge7&\ge4&\ge349.
\end{array}
\tag{NAGC.5.6}
$$

The ordered gate pairs

$$
(2,3),\quad(3,2),\quad(15,16),\quad(16,15)
\tag{NAGC.5.7}
$$

are impossible under both conventions. Removing precisely these
four branches from the inherited $15\cdot14=210$ ordered
unequal pairs leaves at most $206$ unexcluded pairs. This
number counts unexcluded branches, not feasible pairs or covers.

**Proof.** The two distinct gate classes each contribute at least
three to $G$, and every other contribution is nonnegative.
For nonnegative lags, Lemma 4.3 adds $g_0\ge1$. Since the
gate anchors satisfy $3\le r<r+1\le15$, this is a third
distinct class, giving seven rather than six. Theorem 3.2
and $2H^+\ge G$ give the integer moment bounds, and
Theorem 2.2 gives the span bounds.

An adjacent pair in $\{2,\ldots,16\}$ has smaller member
in $\{2,\ldots,15\}$. The necessary range $3\le r\le14$
therefore excludes both orders at $r=2$ and both orders at
$r=15$, exactly the four displayed pairs. The positive
argument includes all native saturated embeddings compatible
with each such pair. Nonnegative covers form a subset, so
the same exclusions hold there. Subtraction gives $210-4=206$;
no construction for any of the remaining branches has been
inferred from this filter. $\square$

## 6. Mathematical attribution and the four existence questions

**Mathematical attribution 6.1 (inherited statements and compound content).**
This volume is a same-theme continuation of [NARC §§13--16][NARC].
Theorems 2.2 and 3.2 concern the full domains of its Theorems 14.2
and 15.2. Their parameter map is the actual original pair $(a,b)$,
its difference $d$, its attained class $C_t$, and its inherited
defect $19-|C_t|$. Neither theorem needs monotonicity or an
individual class's saturated path description. Theorems 4.4,
5.1 and 5.2 additionally consume its complete nineteen-point
normal form, six boundary corners, unequal first-band gates
and, only for the stronger nonnegative bounds, the complete
saturated zero-origin criterion. They do not replace any of
those local results by renamed proofs.

The repo-derived compound content is the simultaneous span and
endpoint accounting on the whole square, its signed rank-moment
coupling to every defect allocation, the corner-budget exclusions
yielding four and five, and second-band exhaustion yielding the
adjacent-gate six/seven bounds and four branch exclusions. The
proofs use ordinary finite double counting, integer rank sums
and the supplied native triple constraints. No worldwide priority
claim is assigned to these deductions.

The primary literature supports the following mathematical
correspondences, within their stated scopes.

| Primary source | Applicable mathematical relation | Boundary of the correspondence |
| --- | --- | --- |
| N. Charpenay, M. Le Treust and A. Roumy, *Optimal Zero-Error Coding for Computing under Pairwise Shared Side Information*, [arXiv:2211.03649v2][CLR], Definitions II.1 and III.1, Theorem III.4 | Unequal target values at one common compatible side-information value require distinct codewords. This is the conflict relation behind the inherited complete-entry collision obstruction. | Their support-restricted probabilistic block model, prefix-free code length and asymptotic chromatic-entropy rate give no two-Read native class certificate or whole-square packing theorem. |
| Robert D. Nowak, *The Geometry of Generalized Binary Search*, [arXiv:0910.4397v5][Nowak], §§I--II, Definition 3 and §V.A | A fixed unknown object has a reply function on the permitted query space. The point-test versus dyadic-subinterval comparison distinguishes available queries from stronger partitions. | Binary hypothesis identification under neighborliness and coherence does not supply the four-reply target-only native bounds or authorize the missing $P_1$. |
| R. Bruno, R. De Prisco, A. De Santis and U. Vaccaro, *Bounds and Algorithms for Alphabetic Codes and Binary Search Trees*, [arXiv:2407.16443v1][BDDSV], abstract and §I | Ordered-search transcripts connect comparison trees and alphabetic codes; binary alphabetic comparisons and ternary search-tree comparisons have different reply structures. | Their probability-weighted average objectives supply neither the six native triples nor an exact grid cover. |

These are literature-attested methods and model distinctions. No
numerical theorem from these papers is invoked for the new gap
bounds, and no matching, matroid, integral-relaxation or topological
sufficiency hypothesis is assumed for the native families. The
comparison is limited to the cited primary statements; it establishes
no exhaustive literature classification or global novelty.

The semantic source correspondences remain those of [NARC,
Mathematical citation 8.1 and Definition 16.2][NARC]: actual ordered
trees and homomorphic substitution, literal constructor replies,
acquired clocks, and the full exterior with its actual hole partition.
The resource restrictions in [NARC §§17--24][NARC] instead concern
one fixed fifteen-origin acquired fiber with installed read/write
control. Those additional restrictions and their optima impose no
condition on Definition 1.2's unrestricted whole-square problem.

**Definition 6.2 (the unresolved existence statements).** Let
$\mathsf{Cover}(q,\lambda)$ mean the existence of one complete
cover in Definition 1.2. The four statements

$$
\mathsf{Cover}(18,1),\qquad \mathsf{Cover}(18,0),\qquad
\mathsf{Cover}(19,1),\qquad \mathsf{Cover}(19,0)
\tag{NAGC.6.1}
$$

remain unresolved here. At eighteen labels, a construction must
select mutually disjoint members of the complete $\mathcal A_t^{\lambda}$
families covering all $324$ cells. An exclusion must address all
defect allocations, both nine-run cases, fused nonmonotone classes
and their complete zero-containing states, as well as saturated
and higher-defect classes. The span and moment equations do not
assert that surviving defect or endpoint data have such a realization.

At nineteen labels, a construction must select a disjoint full
$361$-cell cover from all $\mathcal P_t^+$ or all $\mathcal P_t^0$,
as appropriate. An exclusion must cover every remaining gate branch
and every permitted macro word and integer outer length within it.
The gap lower bounds leave the ranges $G\ge4$ and $G\ge5$,
or $G\ge6$ and $G\ge7$ in adjacent branches, to be addressed
by such an argument. Their feasibility, their sharpness and the
feasibility of any of the at most $206$ unexcluded gate pairs
are not established by the counting constraints.

All statements concern lag recovery on the full inherited native
domain. A two-Read guarantee does not give a uniform address,
workspace, finite-controller or physical-cost bound. The gap count
and rank moments are statistics of one proposed cover, not retained
observer information or an additional source query. These ordinary
mathematical deductions supply no full-original reconstruction,
physical realization or assertion of kernel verification.

[NARC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY_CONTINUATION.md
[NAR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ALPHA_RECUT_MEMORY.md
[AOF]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_ORBIT_RESOURCE_FRONTIER.md
[CLR]: https://arxiv.org/html/2211.03649v2
[Nowak]: https://arxiv.org/html/0910.4397v5
[BDDSV]: https://arxiv.org/html/2407.16443v1

## 追加锚（本行以下为增补区）
