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

## 7. Coordinate residue duplication and projection gaps

**Definition 7.1 (the two projections of one chosen cover).** Fix any
one complete cover $\mathcal C=(C_t)_{t=0}^{18}$ of Definition 1.2
with $q=19$ and $\lambda\in\{0,1\}$. All projection statistics
below refer to these same nineteen chosen classes. Set

$$
\begin{aligned}
S_t^a&=\{a:\exists b,\ (a,b)\in C_t\},&
S_t^b&=\{b:\exists a,\ (a,b)\in C_t\},\\
\gamma_t^a&=\max S_t^a-\min S_t^a-9,&
\gamma_t^b&=\max S_t^b-\min S_t^b-9,\\
\Gamma_a&=\sum_{t=0}^{18}\gamma_t^a,&
\Gamma_b&=\sum_{t=0}^{18}\gamma_t^b,\\
N_i&=\#\{t:i\in S_t^a\},&
M_i&=\#\{t:i\in S_t^b\},\\
\eta_a&=19-N_9,&\eta_b&=19-M_9.
\end{aligned}
\tag{NAGC.7.1}
$$

Here $0\le i\le18$. [NARC, Theorem 13.3][NARC] supplies nine
strict increases of $a$ and nine strict decreases of $b$, with no
returns in either coordinate. Thus $|S_t^a|=|S_t^b|=10$;
$\gamma_t^a,\gamma_t^b$ count the missing integers in their
respective coordinate spans and are nonnegative. Applying the
existing path identity (NAGC.4.1) to this same $C_t$ gives

$$
g_t=\gamma_t^a+\gamma_t^b,\qquad
G(\mathcal C)=\Gamma_a+\Gamma_b.
\tag{NAGC.7.2}
$$

The symbols $N_i,M_i$ are exactly the fixed-first-coordinate and
fixed-second-coordinate incidence counts in [NARC, Theorem 14.3,
(NARC.14.3)][NARC]. In particular

$$
\begin{gathered}
N_i,M_i\in\{4,7,10,13,16,19\},\qquad
\sum_{i=0}^{18}N_i=\sum_{i=0}^{18}M_i=190,\\
\eta_a,\eta_b\in\{0,3,6,9,12,15\}.
\end{gathered}
\tag{NAGC.7.3}
$$

These are inherited projection and incidence facts. The relation
between their residue imbalance and the coordinate span gaps is
provided by the following lemma.

**Lemma 7.2 (one-axis residue charge).** Let
$S_0,\ldots,S_{18}\subseteq\{0,\ldots,18\}$ be any nineteen
sets of cardinality ten. Define

$$
n_i=\#\{t:i\in S_t\},\qquad
\gamma_t=\max S_t-\min S_t-9,\qquad
\Gamma=\sum_{t=0}^{18}\gamma_t.
\tag{NAGC.7.4}
$$

Suppose $n_i\equiv1\pmod3$ for every $0\le i\le18$, and put
$\eta=19-n_9$. Then $\eta\in\{0,3,6,9,12,15,18\}$ and

$$
\Gamma\ge\max\left\{\eta,\ 6+\frac{\eta}{3}\right\}.
\tag{NAGC.7.5}
$$

No path structure or independent covering assumption is needed for
these sets.

**Proof.** For $0\le j\le9$ write

$$
\varepsilon_{t,j}
=\#\{x\in S_t:x\equiv j\pmod{10}\}-1,
\qquad x_+=\max(x,0).
\tag{NAGC.7.6}
$$

Each $S_t$ has ten elements, so
$\sum_{j=0}^{9}\varepsilon_{t,j}=0$. Within $\{0,\ldots,18\}$
a residue has at most two representatives. A positive
$\varepsilon_{t,j}$ is therefore exactly one and occurs precisely
when $0\le j\le8$ and $j,j+10\in S_t$. For $s_t=\min S_t$
and $u_t=\max S_t$, such a duplicate requires
$s_t\le j\le u_t-10$. Since $u_t-s_t\ge9$, this interval
contains $u_t-s_t-9=\gamma_t$ integers, including zero integers
when the span is nine. Consequently

$$
\sum_{j=0}^{9}(\varepsilon_{t,j})_+\le\gamma_t.
\tag{NAGC.7.7}
$$

Thus every duplicated residue in a set is charged to that set's
actual coordinate span gap. Define the aggregate imbalance and its
positive part by

$$
W_j=\sum_{t=0}^{18}\varepsilon_{t,j},\qquad
Q=\sum_{j=0}^{9}(W_j)_+.
\tag{NAGC.7.8}
$$

Taking positive parts after summation cannot increase their total.
Summing (NAGC.7.7) therefore gives the entire charge chain

$$
\Gamma\ge\sum_{t=0}^{18}\sum_{j=0}^{9}
 (\varepsilon_{t,j})_+\ge Q.
\tag{NAGC.7.9}
$$

For $0\le j\le8$ there are two possible representatives of
residue $j$, whereas residue nine has only the representative nine.
Hence

$$
\begin{aligned}
W_j&=n_j+n_{j+10}-19\equiv1\pmod3 &&(0\le j\le8),\\
W_9&=n_9-19=-\eta\le0,&
\sum_{j=0}^{8}W_j&=\eta.
\end{aligned}
\tag{NAGC.7.10}
$$

The sum identity follows from $\sum_jW_j=0$. Also
$0\le n_9\le19$ and $n_9\equiv1\pmod3$, so
$n_9\in\{1,4,7,10,13,16,19\}$, proving the stated range of
$\eta$.

Let $k$ be the number of positive entries among $W_0,\ldots,W_8$.
None of these nine entries is zero. Every positive one is at least
one and every negative one is at most minus two. Their positive
sum is $Q$, because $W_9\le0$, and their negative magnitudes
sum to $Q-\eta$. It follows that

$$
Q\ge k,\qquad
Q-\eta\ge2(9-k)\ge18-2Q,\qquad Q-\eta\ge0.
\tag{NAGC.7.11}
$$

The middle inequality gives $Q\ge6+\eta/3$, and the last gives
$Q\ge\eta$. Together with (NAGC.7.9) these prove (NAGC.7.5).
$\square$

## 8. A universal thirteen-gap bound and necessary equality structure

**Theorem 8.1 (the central anchor couples the actual axes).** Every
chosen complete nineteen-label cover $\mathcal C$ of Definition 1.2,
under either $\lambda=0$ or $\lambda=1$, satisfies

$$
\begin{aligned}
\Gamma_a&\ge\max\left\{\eta_a,6+\frac{\eta_a}{3}\right\},&
\Gamma_b&\ge\max\left\{\eta_b,6+\frac{\eta_b}{3}\right\},\\
\eta_a+\eta_b&\ge3,&G(\mathcal C)&\ge13.
\end{aligned}
\tag{NAGC.8.1}
$$

This quantifies over all twenty permitted macro orders, every initial
point and anchor, and every positive integer outer length admitted by
Definition 1.2; it selects no gate pair, endpoint rule or smaller path
family.

**Proof.** Apply Lemma 7.2 first with $S_t=S_t^a$, $n_i=N_i$,
$\Gamma=\Gamma_a$, $\eta=\eta_a$, and then with $S_t=S_t^b$,
$n_i=M_i$, $\Gamma=\Gamma_b$, $\eta=\eta_b$. Definition 7.1
and the inherited incidence congruences verify all its hypotheses.
Both applications concern the same actual cover $\mathcal C$.

Consider its actual central class $C_9$ and anchor $(9,9)$. This
vertex belongs to a path with nineteen vertices, so it is incident
to at least one edge, including when it is an endpoint. Every edge
is pure. An incident $B$ edge gives at least two vertices of $C_9$
on $a=9$; an incident $A$ edge gives at least two on $b=9$.
By [NARC, Theorem 14.3, part 3][NARC], a nonempty class-line
intersection has size $1+3j$, and hence the indicated intersection
has at least four points. The other classes meeting that same line
each occupy at least one of its nineteen points. Disjointness gives

$$
N_9\le16\quad\hbox{or}\quad M_9\le16.
\tag{NAGC.8.2}
$$

Since both deficits are nonnegative, this proves
$\eta_a+\eta_b\ge3$. Finally the reused identity (NAGC.7.2)
and the two one-axis bounds give

$$
G(\mathcal C)=\Gamma_a+\Gamma_b
\ge12+\frac{\eta_a+\eta_b}{3}\ge13.
\tag{NAGC.8.3}
$$

The central-line argument did not combine separately attainable
projection data: its two incidences and its anchor all belong to
$\mathcal C$. The proof uses the common saturated geometry of both
lag families. A nonnegative-lag cover already satisfies its additional
native first-step condition; no symmetry of that condition or removal
of its zero-lag states is used. $\square$

**Corollary 8.2 (span and signed moment necessities).** Every cover
in Theorem 8.1 satisfies

$$
\sum_{t=0}^{18}(U_t-L_t)\ge355,\qquad H^+=H^-\ge7.
\tag{NAGC.8.4}
$$

**Proof.** Use Theorem 2.2 with $q=19$, the same $C_t$ and the
same $G$: its span total is $342+G$, now at least $355$.
For Theorem 3.2 every $\delta_t=0$, so $H^+=H^-$, and its
classwise inequalities sum to $H^++H^-\ge G$. Thus their
common integer value $H$ satisfies $2H\ge13$ and $H\ge7$.
This is a lower bound on the common moment, not an assertion that
it equals seven. $\square$

**Proposition 8.3 (necessary structure if the gap bound is attained).**
If a cover in Theorem 8.1 has $G(\mathcal C)=13$, then

$$
(\Gamma_a,\Gamma_b;N_9,M_9)
\in\{(6,7;19,16),(7,6;16,19)\}.
\tag{NAGC.8.5}
$$

On the central line with incidence nineteen, each of the nineteen
classes occupies exactly one point. On the other central line,
$C_9$ occupies exactly four points, fifteen other classes occupy
one point each, and three classes are absent. Those four points
are precisely the vertices of one complete pure triple of $C_9$
containing its anchor. These are necessary conditions only.

**Proof.** Let $Q_a,Q_b$ denote the two values of $Q$ in the
applications of Lemma 7.2. Under $G=13$ the complete inequality
chain is

$$
13=\Gamma_a+\Gamma_b
\ge Q_a+Q_b
\ge12+\frac{\eta_a+\eta_b}{3}
\ge13.
\tag{NAGC.8.6}
$$

Every inequality is an equality. In particular
$\eta_a+\eta_b=3$, and (NAGC.7.3) says that both summands
are nonnegative multiples of three. They must therefore be
$(0,3)$ or $(3,0)$. In either order, the individual bounds force
$\Gamma_a=Q_a=6+\eta_a/3$ and
$\Gamma_b=Q_b=6+\eta_b/3$. This proves (NAGC.8.5), with
equality in each axis's charge chain (NAGC.7.9) as well.

Take first $N_9=19$ and $M_9=16$. The nineteen nonempty,
disjoint intersections on $a=9$ partition its nineteen points,
so all are singletons. In particular no $B$ edge of $C_9$ can
be incident to $(9,9)$. At least one incident edge exists, so
it is an $A$ edge. Thus $C_9$ has at least four points on $b=9$.
The sixteen classes meeting this line use at least
$4+15=19$ points; equality is forced by the line's cardinality.
This gives four points for $C_9$, fifteen singleton intersections
and exactly three absent classes.

Because $b$ is nonincreasing along $C_9$, its four vertices on
$b=9$ form one consecutive run. Its three internal edges are
all $A$, and every maximal $A$ run is a concatenation of complete
$AAA$ blocks. A run of exactly three edges is therefore one whole
pure triple. For $N_9=16$, $M_9=19$, the same argument within
the original cover exchanges the coordinate names: the four-point
line is $a=9$ and the triple is $BBB$. This exchange in the proof
does not require transposing a nonnegative-lag cover into another
native-admissible cover. No existence of either configuration is
inferred. $\square$

## 9. Projection supplier correspondence and remaining cover obligations

**Mathematical attribution 9.1 (local parameters and the new coupling).**
The supplier correspondence for Sections 7--8 is as follows.

| Existing result | Parameters used here | Supplied statement and its use |
| --- | --- | --- |
| [NARC, Theorem 14.2][NARC] and Definition 1.2 | $q=19$, the same $\lambda$, original pair $(a,b)$, attained label $t$ and entire class $C_t$ | Exact correspondence between native encoder service and one simultaneous disjoint whole-square cover. |
| [NARC, Theorem 13.3][NARC] | The increasing-$d$ path of each chosen $C_t$; its actual first and second coordinates | Six pure triples, nine changes of each coordinate, ten distinct values on each axis and no coordinate returns. All macro orders and legal positive outer lengths remain in scope. |
| [NARC, Theorem 14.3, part 3][NARC] | Its fixed-first-coordinate count at $i$ is $N_i$; its fixed-second-coordinate count is $M_i$ | Nonempty line intersections have size $1+3j$; the loads satisfy (NAGC.7.3). These supply the hypotheses for Lemma 7.2 and the central-anchor count. |
| Definition 4.1, equation (NAGC.4.1) | The same class $C_t$, its actual coordinate extrema and gap $g_t$ | The existing span decomposition becomes $g_t=\gamma_t^a+\gamma_t^b$ after the two baseline spans of nine are separated. |
| Theorem 2.2 | $q=19$, the actual $D_t,L_t,U_t$ and $G(\mathcal C)$ of Definition 2.1 | The existing total-span identity is $\sum_t(U_t-L_t)=342+G(\mathcal C)$. |
| Theorem 3.2 | The actual positive and negative difference lists of the same classes, with $\delta_t=0$ for every $t$ | The existing identities and inequalities give $H^+=H^-$ and $H^++H^-\ge G(\mathcal C)$. |

The repo-derived increment is the classwise residue-duplication charge
(NAGC.7.7), its combination with the inherited incidence congruences,
and the central anchor's coupling of the two actual projection deficits.
These yield the thirteen-gap necessity and its conditional equality
structure. The span decomposition, projection cardinalities, incidence
congruences and signed-moment identities are reused results, not new
identities. The proofs require no external numerical theorem or
literature-based sufficiency criterion, and make no global novelty claim.

**Scope 9.2 (native contract and unresolved attainment).** Theorem 8.1
keeps Assumption 1.1's genuinely acquired original label, discard of
every other source-bearing field, continuation of that same original,
complete future acquired rows and all permitted lags and cuts. Recovery
still uses at most two chronological native Reads with fully materialized
finite original-root requests, on a stationary current tree and with
termination on every promised input. No finite controller, address or
workspace bound is added. The gap and moment bounds describe selected
cover classes, not physical costs of that service.

The universal necessary range for nineteen-label covers is now
$G\ge13$ under either lag convention. Proposition 8.3 does not
construct a cover, establish sharpness or exclude every larger gap
value. Even excluding its equality configurations would leave all
$G>13$ possibilities to be addressed. The four statements of
Definition 6.2 remain unresolved, as does attainment by an arbitrary
finite producer under the corresponding full native contract.

For $q=18$, Definition 1.2 still admits every allowed defect
allocation, saturated and higher-defect classes, both nine-run cases,
fused nonmonotone classes and every required complete zero-containing
state. Such classes need not have ten distinct values in each
projection or line intersections congruent to one modulo three.
Neither those saturated premises nor the thirteen-gap conclusion is
transferred to the full eighteen-label families. Their general span
and defect-moment identities in Theorems 2.2 and 3.2 retain their
original scope.

## 追加锚（本行以下为增补区）

## 10. Equality in the residue charge of a chosen cover

**Assumption 10.1 (one oriented geometric equality cover).** Retain
Assumption 1.1 and the full families of Definition 1.2. For Sections
10--12, fix one chosen complete positive-lag cover
$\mathcal C=(C_t)_{t=0}^{18}$ with

$$
q=19,\qquad G(\mathcal C)=13,\qquad N_9=19.
\tag{NAGC.10.1}
$$

Every class is the actual chosen member of $\mathcal P_t^+$, with
all twenty macro orders, all initial points, the prescribed diagonal
anchor and all positive integer outer lengths allowed by that family.
Proposition 8.3 supplies, for this orientation,

$$
(\Gamma_a,\Gamma_b;N_9,M_9)=(6,7;19,16).
\tag{NAGC.10.2}
$$

It also supplies equality in both charge chains (NAGC.7.9), singleton
intersections of every class with $a=9$, and exactly one four-point
$AAA$ triple of $C_9$ on $b=9$. Every other class meeting $b=9$
has a singleton intersection. A nonnegative-lag cover is in this
positive geometric family; its extra native condition is the original
first-step condition of [NARC, Theorem 13.4][NARC].

Use the actual projections and gaps of Definition 7.1. Superscripts
$\xi\in\{a,b\}$ on $\varepsilon_{t,j}^\xi,W_j^\xi,Q_\xi$
denote the two applications of (NAGC.7.6)--(NAGC.7.8). Write
$[r,s]_{\mathbb Z}=[r,s]\cap\mathbb Z$. List the ten distinct
first coordinates of $C_t$ as

$$
x_{t,0}<x_{t,1}<\cdots<x_{t,9}.
\tag{NAGC.10.3}
$$

The supplied normal form [NARC, Theorem 13.3][NARC] makes the
second, fifth and eighth $A$ changes unit:
$x_{t,2}-x_{t,1}=x_{t,5}-x_{t,4}=x_{t,8}-x_{t,7}=1$.
Indices in this projection list run from zero to nine, independently
of the zero-to-eighteen indices in the complete path.

**Lemma 10.2 (local saturation, no cancellation and class budgets).**
Under Assumption 10.1 the following properties hold on each axis.
For $S=S_t^\xi$, $s=\min S$, $u=\max S$ and
$\gamma=\gamma_t^\xi$, every pair of representatives available
inside its span is occupied:

$$
\{j,j+10\}\subseteq S
\quad\text{for every }j\in[s,u-10]_{\mathbb Z}.
\tag{NAGC.10.4}
$$

Each missing integer in $[s,u]_{\mathbb Z}\setminus S$ has a
residue absent from $S$ altogether, and distinct such integers have
distinct residues modulo ten. If a residue is duplicated in one
projection on that axis, it is duplicated in exactly one class and
is absent from no class. In particular it cannot be the residue of
a span omission in any other class. The aggregate values are

$$
\begin{array}{c|c|c|c}
\text{axis}&\text{positive }W_j\ (0\le j\le8)
 &\text{negative }W_j\ (0\le j\le8)&W_9\\ \hline
a&\text{six values }1&\text{three values }-2&0\\
b&\text{seven values }1&\text{two values }-2&-3.
\end{array}
\tag{NAGC.10.5}
$$

Consequently

$$
0\le\gamma_t^a\le3,\qquad 0\le\gamma_t^b\le3
\quad(0\le t\le18).
\tag{NAGC.10.6}
$$

If $\gamma>0$, the projection duplicates both residue $s$ and
residue $u-10$, which may be the same residue.

**Proof.** Set $D_t^\xi=\sum_{j=0}^9(\varepsilon_{t,j}^\xi)_+$.
The charge proof in Lemma 7.2 gives $D_t^\xi\le\gamma_t^\xi$.
Proposition 8.3 gives equality in

$$
\Gamma_\xi\ge\sum_tD_t^\xi\ge Q_\xi.
\tag{NAGC.10.7}
$$

All the first differences $\gamma_t^\xi-D_t^\xi$ are
nonnegative, so every one vanishes. Within $[0,18]_{\mathbb Z}$,
$D_t^\xi$ counts exactly the pairs $j,j+10$ occupied by $S$.
The possible lower representatives in its span are precisely
$[s,u-10]_{\mathbb Z}$, containing $\gamma=u-s-9$ integers.
Equality of their count with $D_t^\xi$ proves (NAGC.10.4).

If a span omission had another representative of its residue inside
the span, that pair would be required by (NAGC.10.4), a contradiction.
Representatives outside the span do not belong to $S$ either. Thus
the omission's residue is absent from $S$. Two omissions with one
residue would themselves form one of the required pairs, so this
map from omissions to absent residues is injective.

For a fixed residue and axis, let $P_j$ count classes with
$\varepsilon_{t,j}^\xi=1$ and let $Z_j$ count classes with
$\varepsilon_{t,j}^\xi=-1$. These are the only nonzero values
of $\varepsilon$, and $W_j^\xi=P_j-Z_j$. Hence

$$
\sum_tD_t^\xi-Q_\xi
=\sum_{j=0}^9\bigl(P_j-(P_j-Z_j)_+\bigr)
=\sum_{j=0}^9\min(P_j,Z_j)=0.
\tag{NAGC.10.8}
$$

Each summand is nonnegative. Therefore no residue has both a
duplicating class and an omitting class.

To determine the magnitudes, use (NAGC.7.10)--(NAGC.7.11) at
the supplied values $(Q_a,\eta_a)=(6,0)$ and
$(Q_b,\eta_b)=(7,3)$. On axis $a$, the number $k$ of positive
entries among the first nine obeys $k\le6$ and
$6\ge2(9-k)$, so $k=6$. Their total is six, forcing all six
to be one. The remaining three have total minus six and each is
at most minus two, so all are minus two. Also $W_9^a=0$.
On axis $b$, the inequalities are $k\le7$ and
$7-3\ge2(9-k)$, giving $k=7$. The positive entries are all one,
the other two are minus two, and $W_9^b=-3$. This proves
(NAGC.10.5). At a duplicated residue, no cancellation and
$W_j^\xi=1$ now give $P_j=1$ and $Z_j=0$.

Each axis has precisely three residue types with negative aggregate
value. The injective omission-to-residue map above must take its
values in those types, by no cancellation. Since a projection has
exactly $\gamma_t^\xi$ omissions in its span, (NAGC.10.6) follows.
Finally $\gamma>0$ makes $s\le u-10$, so both endpoints of
this interval supply pairs in (NAGC.10.4). $\square$

## 11. Exact center ownership and exhaustion of the lower boundary

**Lemma 11.1 (center points, forced row segments and anchor ranks).**
Under Assumption 10.1, the actual classes satisfy

$$
\begin{aligned}
&(9,t)\in C_t &&(0\le t\le18),\\
&(a,t)\in C_t
 &&\bigl(\min(t,9)\le a\le\max(t,9),\ a\in\mathbb Z\bigr),\\
&S_0^a=[0,9]_{\mathbb Z},\qquad
 S_{18}^a=[9,18]_{\mathbb Z}.&
\end{aligned}
\tag{NAGC.11.1}
$$

For every $(a,b)\in C_t$, one has $b\ge t$ if $a<9$ and
$b\le t$ if $a>9$. The zero-based rank of $t$ in the increasing
list of $S_t^b$ belongs to $\{0,3,6,9\}$.

**Proof.** Proposition 8.3 supplies one point $(9,b_t)$ from each
class on $a=9$, with all $b_t$ distinct. The belt inequality in
[NARC, Theorem 14.3, part 1][NARC] gives $b_t\le t$ for
$t<9$, and $b_t\ge t$ for $t>9$. Also $b_9=9$ by the anchor.
For $t=0$, the former inequality forces $b_0=0$. Inductively,
if the values $0,\ldots,t-1$ already belong to their respective
classes, distinctness and $0\le b_t\le t$ force $b_t=t$.
This proves the assertion for $t<9$. Descending induction from
$t=18$, using $t\le b_t\le18$, gives the assertion for $t>9$.
Thus $(9,t)$ is the actual center-line point of $C_t$.

The first coordinate never decreases along a chosen path and the
second never increases. Every point of $C_t$ with $a<9$ is
therefore before $(9,t)$ and has $b\ge t$; every point with
$a>9$ is after it and has $b\le t$.

Now fix an integer $t\le a<9$ and let $C_j$ own $(a,t)$ in
the complete cover. The belt gives $t\le j\le a$, while the
preceding inequality applied to $C_j$ gives $t\ge j$.
Hence $j=t$. For $9<a\le t$ the belt instead gives
$a\le j\le t$ and the center-line inequality gives $t\le j$,
again forcing $j=t$. The cases $a=9$ are already known.
This proves the entire row segment in (NAGC.11.1): every indicated
cell has its owner fixed within this same cover.

For $t=0$ and $18$ these segments contain ten distinct first
coordinates. Each projection has exactly ten elements by Definition
7.1, so they exhaust $S_0^a$ and $S_{18}^a$ respectively.

No $B$ edge can be incident to $(9,t)$, because it would give
a second point of $C_t$ on $a=9$. Every $B$ triple is consequently
entirely before or entirely after that point. The number of $B$
changes after it is one of $0,3,6,9$. Each such change reaches a
new and strictly smaller second coordinate; these are precisely
the elements of $S_t^b$ smaller than $t$. Their number is its
zero-based rank, proving the last assertion. $\square$

**Lemma 11.2 (four actual classes on the lower boundary).** Under
Assumption 10.1, if $C_t$ meets $b=0$ and $\gamma_t^b=0$,
then

$$
S_t^b=[0,9]_{\mathbb Z},\qquad t\in\{0,3,6,9\}.
\tag{NAGC.11.2}
$$

At most one class meeting $b=0$ has $\gamma_t^b>0$, and

$$
M_0=4.
\tag{NAGC.11.3}
$$

In particular, if $C_3,C_6,C_9$ all have second-coordinate
projection $[0,9]_{\mathbb Z}$, the classes meeting $b=0$
are exactly $C_0,C_3,C_6,C_9$.

**Proof.** A class meeting $b=0$ has $\min S_t^b=0$.
If its gap is zero, its ten coordinates occupy all of
$[0,9]_{\mathbb Z}$. The anchor's second coordinate $t$ is
then its own zero-based rank. Lemma 11.1 restricts that rank to
$0,3,6,9$, proving (NAGC.11.2).

If instead $\gamma_t^b>0$, Lemma 10.2 requires both zero and
ten in $S_t^b$. Thus this class duplicates residue zero. That
lemma allows only one duplicating class per residue on an axis,
so there is at most one such positive-gap boundary class. There
are at most four zero-gap boundary classes, by their distinct
labels in (NAGC.11.2). Consequently $M_0\le4+1=5$.

The incidence supplier (NAGC.7.3), equivalently [NARC, Theorem
14.3, part 3][NARC], applies to this complete saturated cover.
It gives both $M_0\ge4$ and $M_0\equiv1\pmod3$. The only
integers between four and five are four and five; five has residue
two modulo three. Thus these three conditions force $M_0=4$.
Finally $C_0$ always meets $b=0$ at its anchor. Under the stated
additional hypothesis, $C_3,C_6,C_9$ do also. These are four
distinct classes and exhaust the incidence count. $\square$

## 12. The actual three-class boundary collision

**Lemma 12.1 (three unit second-coordinate projections are impossible).**
No cover satisfying Assumption 10.1 can have

$$
S_3^b=S_6^b=S_9^b=[0,9]_{\mathbb Z}.
\tag{NAGC.12.1}
$$

**Proof, the common boundary and the supplied corner arms.** Suppose
(NAGC.12.1) holds in the fixed cover $\mathcal C$. Its three
indicated paths have all nine $B$ lengths equal to one. Their $A$
triples can therefore occur only at second coordinates $9,6,3,0$:
any $A$ triple occurs after zero, one, two or three complete $B$
triples. All three paths start at $b=9$ and end at $b=0$.
For every label put

$$
F_t=\{a:(a,0)\in C_t\}.
\tag{NAGC.12.2}
$$

These sets refer to intersections of the chosen classes, not to
independently selected paths. Lemma 11.2 says that only the labels
$0,3,6,9$ meet $b=0$. By [NARC, Theorem 14.3, part 1][NARC],
$C_0$ is the $B^9A^9$ path with corner $(0,0)$. Its entire
first-coordinate projection occurs on its horizontal arm. Lemma 11.1
therefore gives $F_0=[0,9]_{\mathbb Z}$, and complete disjoint
coverage gives

$$
[10,18]_{\mathbb Z}=F_3\sqcup F_6\sqcup F_9.
\tag{NAGC.12.3}
$$

The same corner supplier gives, for $j=0,1,2$, a fixed-first-coordinate
arm of $C_j$ consisting of all $(j,b)$ with $b\in S_j^b$, where

$$
\min S_j^b=j,\qquad
\max S_j^b=j+9+\gamma_j^b\ge j+9.
\tag{NAGC.12.4}
$$

Lemma 10.2 bounds the number of omitted integers in each of these
spans by three. Thus four distinct points of a different class on
$a=j$, whose second coordinates lie in this span, would already
contradict disjointness. This uses the actual vertical arm of $C_j$.

**Proof, the forced path of $C_3$.** Since $C_3\ne C_9$,
Proposition 8.3 makes its intersection with $b=9$ a singleton.
It consequently begins with a $BBB$ triple. Write its initial first
coordinate as $s$. The anchor gives $s\le3$. If $s=0$, its
first triple occupies $(0,b)$ for $b=6,7,8,9$. These four second
coordinates lie in the span of $S_0^b$ by (NAGC.12.4). Disjointness
would omit all four from that projection, contrary to its budget.
Hence $s\ge1$.

No $A$ triple can occur before the path reaches $b=3$: one such
triple would increase the first coordinate to at least $s+3\ge4$,
after which the anchor $(3,3)$ could not be reached. It therefore
makes its first six unit $B$ changes at $a=s$ and occupies all
$(s,b)$ with $3\le b\le9$. If $s=1$ or $2$, these seven
second coordinates lie in the span (NAGC.12.4) of $C_s$.
Disjointness would force seven omissions there, again contradicting
Lemma 10.2. Thus $s=3$.

Lemma 11.1 puts every $(a,3)$ with $3\le a\le9$ in $C_3$.
Three $B$ changes remain after this row, because its terminal second
coordinate is zero. The row cannot be left at $a<9$, since it must
first contain $(9,3)$, and it cannot be left at $a=9$, since the
next $B$ edge would add another point to its singleton intersection
with $a=9$. Thus its row $b=3$ contains those seven points and
at least one further point with $a>9$.

By [NARC, Theorem 14.3, part 3][NARC], a nonempty class-row
intersection has size $1+3j\le10$. A size of at least eight
therefore forces size ten. All nine $A$ changes occur on that row.
The path and its first-coordinate endpoint are consequently

$$
C_3:\ B^6A^9B^3,\qquad
\min S_3^a=3,\qquad
u:=\max S_3^a=12+\gamma_3^a\in[12,15]_{\mathbb Z},
\qquad F_3=\{u\}.
\tag{NAGC.12.5}
$$

The notation $B^6A^9B^3$ specifies directions; the $A$ lengths
retain their allowed values. In particular the first seven entries
of its projection are

$$
x_{3,i}=3+i\quad(0\le i\le6).
\tag{NAGC.12.6}
$$

**Proof, the restrictions on $C_6$ and $C_9$.** The intersection
of $C_6$ with $b=9$ is also a singleton, so it starts with a
unit $BBB$ triple. Let $s=\min S_6^a$ be its initial first
coordinate. For $s=0,1,2$, its four initial second coordinates
$6,7,8,9$ are all inside the corresponding corner span in
(NAGC.12.4), giving the same four-omission contradiction. If
$s=3$, these initial points intersect the fixed segment of $C_3$
at $a=3$, $3\le b\le9$, just established. The anchor of $C_6$
then gives

$$
4\le s\le6.
\tag{NAGC.12.7}
$$

The forced row segment of Lemma 11.1 puts $a=6,7,8,9$ on
$b=6$ in $C_6$. Six unit $B$ changes remain after this row.
The same singleton-center argument requires the row to extend
beyond $a=9$ before those changes begin. It has at least five
points, so the supplied $1+3j$ intersection law makes it have
at least seven. Thus at least two of the three $A$ triples of
$C_6$ occur on $b=6$. At most one $A$ triple remains for
$b=0$, whence

$$
|F_6|\in\{1,4\}.
\tag{NAGC.12.8}
$$

For $C_9$, Proposition 8.3 supplies exactly four points on $b=9$,
forming one complete $AAA$ triple containing $(9,9)$. Since the
path starts at $b=9$ and never returns after a $B$ change, this
is its first $A$ triple and its first macro block. It uses
$x_{9,0},x_{9,1},x_{9,2},x_{9,3}$. The anchor nine cannot be
$x_{9,3}$: the next block is $BBB$ and would then supply another
point on $a=9$. Thus for some $r\in\{0,1,2\}$,

$$
x_{9,r}=9,\qquad x_{9,3}>9.
\tag{NAGC.12.9}
$$

Together, (NAGC.12.3), $|F_3|=1$ and (NAGC.12.8) leave
exactly the two terminal allocations

$$
(|F_6|,|F_9|)=(1,7)\quad\text{or}\quad(4,4).
\tag{NAGC.12.10}
$$

Indeed, their sizes must sum to eight. In the first allocation,
$C_9$ uses its two remaining $A$ triples at $b=0$, so
$F_9=\{x_{9,3},\ldots,x_{9,9}\}$. In the second allocation,
its last $A$ triple is at $b=0$, its middle $A$ triple is at
$b=6$ or $3$, and $F_9=\{x_{9,6},\ldots,x_{9,9}\}$.
These are all possibilities under the stated hypotheses, because
there are exactly three $A$ triples per class and second coordinates
never return.

**Proof, allocation $(1,7)$.** The singleton $F_6$ is the maximum
first coordinate of $C_6$, at least $s+9\ge13$. Also $u\ge12$
by (NAGC.12.5). Hence the two smallest coordinates ten and eleven
in (NAGC.12.3) both belong to $F_9$. They must be its first two
values $x_{9,3}=10$ and $x_{9,4}=11$. The supplied unit fifth
$A$ change makes $x_{9,5}=12$, so twelve also belongs to $F_9$.
Disjointness now gives $u\ge13$, and therefore
$\gamma_3^a=u-12>0$.

Apply (NAGC.10.4) to the actual projection $S_3^a$, with
$s=3$ and maximum $u$. It requires the pair $u-10,u$, so
$C_3$ duplicates residue $u-10$. On the other hand $u\le15$,
and at least two of $16,17,18$ belong to $F_9$: $F_3=\{u\}$
contains none of them and $F_6$ can contain at most one. Thus
$S_9^a$ has a value above $u$ as well as the value ten below it.
The coordinate $u$ is absent from $F_9$ by boundary disjointness.
Every first coordinate of $C_9$ preceding $F_9$ is one of
$x_{9,0},x_{9,1},x_{9,2}$ and is strictly smaller than ten.
It follows that $u$ is absent from $S_9^a$ altogether while
lying inside its span.

Lemma 10.2 therefore makes residue $u-10$ absent from $S_9^a$.
This contradicts no cancellation with its duplication in $S_3^a$.
Both projections are those of the same classes furnishing the
partition (NAGC.12.3), so the contradiction concerns the chosen
cover itself.

**Proof, allocation $(4,4)$.** Here (NAGC.12.9) and positivity
of all $A$ lengths give

$$
\min F_9=x_{9,6}\ge x_{9,r}+(6-r)\ge13.
\tag{NAGC.12.11}
$$

Since $u\ge12$, neither ten nor eleven can belong to $F_3$ or
$F_9$. Hence both belong to $F_6$. Its four points constitute
its last $A$ triple, namely $x_{6,6},x_{6,7},x_{6,8},x_{6,9}$.
The boundary partition gives $x_{6,6}=10$, $x_{6,7}=11$, and
the unit eighth $A$ change gives $x_{6,8}=12$. Put
$v=x_{6,9}\ge13$. The six earlier $A$ changes go from the
initial coordinate $s\ge4$ to $x_{6,6}=10$. Their total is
at least six, so $s=4$ and all six lengths are one. Therefore

$$
S_6^a=[4,12]_{\mathbb Z}\cup\{v\},\qquad
F_6=\{10,11,12,v\},\qquad v\ge13.
\tag{NAGC.12.12}
$$

If $v\ge15$, the interval of pairs required by (NAGC.10.4)
contains the lower representative four and requires $4,14$ in
$S_6^a$. Formula (NAGC.12.12) omits fourteen whenever $v\ge15$.
Thus $v=13$ or $14$.

Twelve now belongs to $F_6$, so $u\ge13$. Saturation of
$S_3^a$, whose minimum is three, requires the pair $3,13$:
$C_3$ duplicates residue three. If $v=14$, the span of $S_6^a$
contains its omitted integer thirteen. Lemma 10.2 would then
make that same residue three absent from $S_6^a$, violating no
cancellation. Consequently

$$
v=13,\qquad u\ge14.
\tag{NAGC.12.13}
$$

The latter inequality uses $u\ne13$, since thirteen is now in
$F_6$. Local saturation of $S_3^a$ requires both pairs $3,13$
and $4,14$. Its first seven values are fixed by (NAGC.12.6),
so thirteen and fourteen are among $x_{3,7},x_{3,8},x_{3,9}$.
In particular $x_{3,8}\ge13$. The unit eighth $A$ change gives
$x_{3,7}=x_{3,8}-1\ge12$. There is therefore no place for ten
or eleven in this projection:

$$
10,11\notin S_3^a.
\tag{NAGC.12.14}
$$

Eleven lies inside the span $[3,u]_{\mathbb Z}$. Lemma 10.2
makes residue one absent from $S_3^a$. The actual corner class
$C_1$ has $\min S_1^a=1$ by [NARC, Theorem 14.3, part 1][NARC].
If $\gamma_1^a>0$, its local saturation would require the pair
$1,11$, contradicting no cancellation on the first axis. Thus
$\gamma_1^a=0$, and its ten coordinates fill $[1,10]_{\mathbb Z}$.
The same corner supplier puts its entire $A$ arm on $b=1$.
Hence

$$
(10,1)\in C_1.
\tag{NAGC.12.15}
$$

In this allocation, $C_6$ uses its last $A$ triple at $b=0$
and at least two at $b=6$, so exactly its first two $A$ triples
occur at $b=6$. By (NAGC.12.12) they go from first coordinate
four to ten. Its two remaining unit $BBB$ triples then go from
$b=6$ to $b=0$ at the fixed first coordinate ten, before the
last $A$ triple starts. They contain $(10,1)$. Thus

$$
(10,1)\in C_6,
\tag{NAGC.12.16}
$$

contradicting (NAGC.12.15) and the disjointness of $C_1$ and
$C_6$ in $\mathcal C$. Both terminal allocations have now led
to contradictions within the same chosen cover. This proves the
lemma. $\square$

## 13. Extreme-class rigidity and the nonnegative fourteen-gap necessity

**Theorem 13.1 (both extreme anchor classes are unit at equality).**
Every chosen complete positive geometric cover $\mathcal C$ of
Definition 1.2 with $q=19$ satisfies

$$
G(\mathcal C)=13\quad\Longrightarrow\quad g_0=g_{18}=0.
\tag{NAGC.13.1}
$$

Thus equality forces every edge of both extreme anchor classes to
have unit length. The assertion quantifies over the full family
$\mathcal P_t^+$ for each anchor, without a restriction on the
macro words, initial points or positive outer lengths beyond
Definition 1.2.

**Proof, the lower extreme in the orientation $N_9=19$.** Assume
$G=13$ and $N_9=19$. All hypotheses of Assumption 10.1 hold.
Lemma 11.1 gives $S_0^a=[0,9]_{\mathbb Z}$ and
$\gamma_0^a=0$. Suppose $\gamma_0^b>0$. Since $(0,0)\in C_0$,
its second-coordinate projection has minimum zero. Lemma 10.2
makes it duplicate residue zero. The same lemma forbids any other
class meeting $b=0$ from having positive second-coordinate gap,
because that class would also duplicate residue zero.

Lemma 11.2 gives exactly four classes meeting $b=0$. Apart from
$C_0$, the other three must therefore have zero second-coordinate
gap, projection $[0,9]_{\mathbb Z}$ and labels in $\{0,3,6,9\}$.
Their labels are distinct and none is zero, so they are precisely
$C_3,C_6,C_9$. This contradicts Lemma 12.1. Hence
$\gamma_0^b=0$. The existing identity (NAGC.7.2) for this same
class gives $g_0=\gamma_0^a+\gamma_0^b=0$.

**Proof, the upper extreme and the other orientation.** Consider
coordinate complementation and transposition, with transformed
classes relabeled by their transformed anchors:

$$
\begin{aligned}
R(a,b)&=(18-a,18-b),&
 \mathcal C^R_t&=R(C_{18-t}),\\
T(a,b)&=(b,a),&
 \mathcal C^T_t&=T(C_t).
\end{aligned}
\tag{NAGC.13.2}
$$

For either transformation, reverse each path list to restore
increasing difference order. These are bijections of the square,
so they preserve complete disjoint coverage. Under $R$ an original
$A$ edge reversed becomes an $A$ edge of the same length, and
likewise for $B$; under $T$ the reversed edges exchange $A$ and
$B$. Reversal takes each complete triple to a complete triple
and preserves its middle edge. Thus each transformation preserves
the six-triple normal form with three triples of each direction,
all positive lengths and the unit-middle conditions. The transformed
anchor is exactly the one used in (NAGC.13.2), and strict increase
of the transformed difference excludes any other diagonal point.
Each image class is therefore a nineteen-point subset satisfying
every hypothesis of the converse in [NARC, Theorem 13.3][NARC].
That converse supplies both-cut readability at every positive lag,
so each image class belongs to the full family $\mathcal P_t^+$
of Definition 1.2. Together with the preserved disjoint whole-square
coverage, [NARC, Theorem 14.2][NARC] supplies the same full native
encoder-service contract for each image cover. These are thus
positive geometric covers. The existing identity (NAGC.4.1) gives

$$
G(\mathcal C^R)=G(\mathcal C^T)=G(\mathcal C),\qquad
 g_t(\mathcal C^R)=g_{18-t}(\mathcal C),\qquad
 g_t(\mathcal C^T)=g_t(\mathcal C).
\tag{NAGC.13.3}
$$

Complementation preserves the line $a=9$ and its incidence count.
For the orientation already treated, $\mathcal C^R$ therefore
satisfies $G=13$ and $N_9=19$. Applying the lower-extreme result
to this cover yields $g_0(\mathcal C^R)=0$, hence
$g_{18}(\mathcal C)=0$ as well.

Finally, Proposition 8.3 says every equality cover has either
$(N_9,M_9)=(19,16)$ or $(16,19)$. In the latter case $T$
exchanges the two incidence counts, so $\mathcal C^T$ has
$N_9=19$. The two extreme conclusions just proved apply to it,
and (NAGC.13.3) transfers both to the original $\mathcal C$.
This exhausts the alternatives in Proposition 8.3.

All these transformations act within the positive geometric family.
No invariance of the additional nonnegative first-step condition is
used. Finally (NAGC.4.1) expresses $g_t$ as the sum of the eighteen
nonnegative integers $\ell_i-1$. Its vanishing is exactly the
assertion that all eighteen lengths are one. $\square$

**Theorem 13.2 (the original nonnegative-lag cover needs fourteen gaps).**
For every chosen complete cover $\mathcal C$ of Definition 1.2 with
$q=19$ and $\lambda=0$,

$$
G(\mathcal C)\ge14,\qquad
\sum_{t=0}^{18}(U_t-L_t)\ge356.
\tag{NAGC.13.4}
$$

These are necessary inequalities for the chosen cover, with $G$
counting the missing integer differences of Definition 2.1, including
class multiplicity. They are not counts of uncovered cells or prices
of native Reads.

**Proof.** Theorem 8.1 already gives $G(\mathcal C)\ge13$.
Suppose equality holds. Each $\mathcal P_t^0$ is a subfamily of
$\mathcal P_t^+$, so Theorem 13.1 applies to this very cover and
gives $g_0=0$. Return now to the actual original class $C_0$,
with the original coordinate roles and the original lag convention.
[NARC, Theorem 14.3, part 1][NARC] supplies its $B^9A^9$ order
and corner $(0,0)$. Theorem 13.1 makes all its lengths unit;
therefore its first point is $(0,9)$ and its first edge is the
unit $B$ edge to $(0,8)$.

This is exactly the excluded conjunction in [NARC, Theorem
13.4][NARC]: initial first coordinate zero and a unit first $B$
edge. That theorem's saturated-class hypothesis holds because
$C_0$ has nineteen points and the supplied normal form, and its
full native readability hypothesis is precisely the requirement
$C_0\in\mathcal P_0^0$ of Definition 1.2. It excludes this
original class under $\lambda=0$. Thus $G=13$ is impossible
in the original nonnegative-lag cover. Integrality and the already
supplied lower bound give $G\ge14$.

Theorem 2.2, applied to the same $q=19$, class difference sets
and gap count, gives $\sum_t(U_t-L_t)=342+G\ge356$.
The zero-lag gate has been applied only to the original $C_0$;
none of the geometric symmetries in Theorem 13.1 is asserted to
preserve that asymmetric gate. $\square$

## 14. Equality suppliers and the remaining existence questions

**Mathematical attribution 14.1 (consumed premises and joint deductions).**
Theorems 13.1 and 13.2 use the following supplier correspondence.
All class parameters refer to a single chosen complete cover at each
application.

| Supplier | Exact specialization | Role in the deductions |
| --- | --- | --- |
| Assumption 1.1, Definition 1.2 and [NARC, Definition 14.1 and Theorem 14.2][NARC] | $q=19$; all $C_t\in\mathcal P_t^+$ for the geometric theorem; the original $C_t\in\mathcal P_t^0$ for the nonnegative theorem | Complete disjoint whole-square coverage with every anchor, macro order and legal outer length, under the inherited acquired-label and same-original native service contract. |
| Theorem 8.1 and Proposition 8.3 | $G(\mathcal C)=13$ on that whole family | The existing thirteen-gap lower bound, the two axis-budget alternatives, equality in both residue charge chains, nineteen singleton center-line intersections and the other central line's unique four-point triple. |
| Lemma 7.2 and (NAGC.7.6)--(NAGC.7.11) | First $S_t=S_t^a$, then $S_t=S_t^b$, for those same nineteen classes | The residue variables and inequalities whose equality yields local saturation, no cancellation and the three-omission class budgets in Lemma 10.2. |
| [NARC, Theorem 13.3][NARC] | The actual increasing-$d$ path and its increasing first-coordinate list $x_{t,0},\ldots,x_{t,9}$; the reversed image paths under $R$ and $T$ | Whole pure triples, monotonicity, nine changes per axis, and unit second, fifth and eighth coordinate changes. These determine the anchor rank restriction and the terminal triples in Lemma 12.1. The converse certifies the positive-lag readability of each transformed class in Theorem 13.1. |
| [NARC, Theorem 14.3, part 1][NARC] | The belt at every actual point; the corner classes with labels $0,1,2,18$ | Exact center-point ownership, the vertical arms excluding initial coordinates zero through two, the original $C_0$ corner, and the horizontal $C_1$ arm containing the final collision point. |
| [NARC, Theorem 14.3, part 3][NARC] and (NAGC.7.3) | The actual rows $b=0,3,6,9$ and center line $a=9$ | Sizes $1+3j$ of nonempty intersections, $M_0\ge4$ and $M_0\equiv1\pmod3$, combined with $M_0\le5$ to exhaust the four boundary owners and the two terminal allocations. |
| (NAGC.7.2) and (NAGC.4.1) | The original or explicitly transformed class with its actual coordinate spans and edge lengths | Conversion of the two projection gaps to $g_t$, preservation of $G$ under the geometric symmetries, and unit lengths when $g_t=0$. |
| [NARC, Theorem 13.4][NARC] | Only the original $C_0\in\mathcal P_0^0$, after Theorem 13.1 gives $g_0=0$ | The saturated nonnegative-lag first-step exclusion at $(0,9)\to(0,8)$. |
| Theorem 2.2 | The same original nonnegative cover, $q=19$ and $G(\mathcal C)\ge14$ | The exact span identity giving the necessary total $356$. |

The repo-derived content is the equality refinement of the residue
charge, its exact center and boundary ownership consequences, the
two-allocation collision in one common cover, and the resulting
extreme-class rigidity and fourteen-gap necessity. The inherited
thirteen-gap theorem, native normal form, corner geometry, incidence
law and zero-lag criterion remain the direct premises. No numerical
conclusion from external tiling literature is invoked, and no worldwide
priority or absence-of-publication claim is assigned to these deductions.

**Definition 14.2 (necessary ranges and unresolved attainment).** Retain
$\mathsf{Cover}(q,\lambda)$ as the existence statement of Definition
6.2. For a chosen nineteen-label cover, the necessary ranges furnished
by Theorems 8.1, 13.1 and 13.2 are

$$
\begin{array}{c|c}
\text{lag convention}&\text{necessary conditions on a chosen cover }\mathcal C\\ \hline
\lambda=1&G(\mathcal C)\ge13,\quad
 G(\mathcal C)=13\ \Longrightarrow\ g_0=g_{18}=0\\
\lambda=0&G(\mathcal C)\ge14,\quad
 \sum_t(U_t-L_t)\ge356.
\end{array}
\tag{NAGC.14.1}
$$

A bound on $G(\mathcal C)$ is conditional on that chosen complete
cover; it is not an assignment of a gap count to the existential
proposition $\mathsf{Cover}(q,\lambda)$. All four existence
questions $\mathsf{Cover}(18,0)$, $\mathsf{Cover}(18,1)$,
$\mathsf{Cover}(19,0)$ and $\mathsf{Cover}(19,1)$ remain unresolved.
In particular the existence of a positive-lag cover with $G=13$,
sharpness of either necessary range, a complete cover construction
and attainment by an arbitrary finite producer remain unresolved.

At eighteen labels the full families of Definition 1.2 still admit
all their defect allocations, saturated and higher-defect classes,
both nine-run cases, fused nonmonotone classes and complete
zero-containing states. The ten-value projections and saturated
line-intersection law used here are not supplied for that whole
family. No eighteen-label gap bound or existence obstruction is
inferred from the equality argument.

The native contract remains Assumption 1.1: genuine original
acquisition and export, discard of all other source-bearing data,
continuation of the same original, complete future acquired rows,
all permitted cuts and lags, and at most two chronological native
Reads with materialized finite original-root words and termination
on every promised input. The complete current tree is stationary
during those Reads. No fixed finite controller, address limit,
workspace limit or physical-cost bound is imposed by these necessary
cover inequalities.

## 追加锚（本行以下为增补区）
