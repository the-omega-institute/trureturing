[Index](../../../marked_head_profile.md) · [Protected cofactor-dependent codes](850-cofactor-dependent-protected-codes.md) · [Grouped shallow slots](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment)

# Protected-digit inventory and grouped inverse hulls

Numerical divisor closure, a private point for every original,
the GHA11 individual-prime height upper bounds, initial-segment
odd-prime support through 113, and complete actual $C_1$
occupancy of every allowed cell at $q=113$ do not force a
movable digit. The explicit family below has 6,200 distinct
odd nonunit classes satisfying those conditions, while every
first-digit owner-cofactor gcd is one. Thus every nontrivial
control modulus has $D_h=\varnothing$.

This family is a noncover. It fails stronger mixed-height
profiles and the Report 388, Section 74 conditions at other
large primes. It does not show that an EB1 whole cover can
have empty movable inventory, or exclude a protected-code
argument using whole coverage or simultaneous prime relations.
A separate sufficient criterion groups all q-heights at the
same actual cofactor and pays complete inverse hulls with
fresh ternary labels. No code satisfying that criterion for
every group of an actual EB1 family is supplied.

The notation $D_h,g_c$ and the protected-code interface are
from [Report 850, CD1--CD10](850-cofactor-dependent-protected-codes.md).
SC labels refer to
[Report 388](../350-399/388-source-global-substitution-collision-moment.md),
and GHA11 and DP12 refer to
[Report 385](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md).
All results here are ordinary mathematical deductions, without
a claim of Lean verification or a resolution of Erdős #7.

## 1. What missing movable inventory supplies

Consider an actual original family in the height-two setting
of Report 388, Section 74. Write its q-bearing labels as
$3^aq^em$ with $0\le a\le2$, $1\le e\le G$, and
$(m,3q)=1$. For a control $h>1$ dividing $W$, let
$B_h=\mathbb F_q\setminus D_h$, let $J_h$ be the actual
q-bearing originals with $h\nmid m$, and let $C_h$ be
their distinct numerical cofactors. Then

$$
\begin{gathered}
B_h=\{\rho_d\bmod q:d\in J_h\},\qquad
q-|D_h|\le|J_h|,\\
|C_h|\ge\left\lceil\frac{q-|D_h|}{3G}\right\rceil,\\
|C_h\setminus\{1\}|\ge
\left\lceil\frac{\max(0,q-|D_h|-3G)}{3G}\right\rceil.
\end{gathered}
\tag{IG1}
$$

Choose one witness at each bad digit. These witnesses have
distinct numerical labels because each original has only one
first q-digit. At a fixed cofactor there are at most $3G$
labels, including at most $3G$ labels with unit cofactor.
This proves all three bounds with actual phases and all
q-heights retained.

At $q=113$, GHA11 gives $G\le10$. When $25\mid W$,
failure of the paired-row entrance $|D_{25}|\ge60$ from
Report 850 leaves at least 54 bad digits. IG1 then gives at
least two distinct cofactors and at least one nonunit cofactor.
At $G=1$, the corresponding bounds are 18 cofactors and 17
nonunit cofactors. These counts do not contradict the known
inventories.

The witnesses need not have small cofactor support. Replacing
an actual witness by a numerical divisor reduces its cofactor
but need not preserve its actual q-digit. Divisor closure
does not give a phase-preserving map between original classes.
The construction below makes this distinction explicit: 109
bad digits have no owner with at most two cofactor primes.

## 2. A parameterized family with private points

Fix a prime $q>27$ and a set
$P=\{p_1,\ldots,p_n\}$ of distinct primes satisfying

$$
6n<p_i<q\quad(1\le i\le n),\qquad
2^n-1\ge5q-11,\qquad
2^{n-1}-1\ge q-2.
\tag{IG2}
$$

For a residue class write $[r]_d=\{x:x\equiv r\pmod d\}$.
Take safe words $\mathcal A=\{2,4,5,7,8\}$ modulo 9 and
the five cofactor-free original classes

$$
\begin{aligned}
A_3&=[0]_3,& A_9&=[1]_9,& A_q&=[0]_q,\\
A_{3q}&=[1]_3\cap[1]_q,&
A_{9q}&=[2]_9\cap[2]_q.
\end{aligned}
\tag{IG3}
$$

Thus $\alpha=0$, $\beta=1$, $\gamma=2$, and $\zeta=2$.
The permitted final cells are

$$
\mathcal L=\{(c,z):2\le c<q,\ z\in\mathcal A,
                         \ (c,z)\ne(2,2)\},
\qquad |\mathcal L|=5q-11.
\tag{IG4}
$$

For each nonempty $S\subseteq P$, put $m_S=\prod_{p\in S}p$
and assign a cell $(c_S,z_S)\in\mathcal L$. First select
$q-2$ distinct unordered complementary pairs
$\{S,P\setminus S\}$ with both members nonempty. Give
one pair to each row $c=2,\ldots,q-1$, assigning its two
members different allowed words in that row. Fill every
remaining cell with a different unused nonempty subset, and
send all leftover subsets to $(3,4)$. IG2 supplies enough
pairs and subsets. Every cell is occupied, and each row has
two coprime cofactors.

Use the full numerical divisor set and tag

$$
\begin{gathered}
D_{\rm core}=\{3^aq^jm_S:0\le a\le2,\ 0\le j\le1,
                         \ S\subseteq P\}\setminus\{1\},\\
t(a,j,s)=1+a+3j+6(s-1)\qquad(1\le s\le n).
\end{gathered}
\tag{IG5}
$$

The tag lies in $\{1,\ldots,6n\}$, below every palette
prime, and determines $(a,j,s)$ uniquely. For nonempty $S$,
define the actual class of $3^aq^jm_S$ by CRT with the
following coordinates:

| Coordinate present in the modulus | Actual residue |
| --- | --- |
| Each $p\in S$ | $t(a,j,|S|)$ modulo $p$ |
| $q$, when $j=1$ | $c_S$ |
| $3$, when $a=1$ | $z_S$ modulo 3 |
| $9$, when $a=2$ | $z_S$ |

At $a=0$ or $j=0$ the corresponding coordinate is
unrestricted. Empty-$S$ labels use IG3. These are distinct
odd nonunit moduli with $H_3=2$, $H_q=1$, and height one
at every palette prime; their cofactor carrier is
$W=\prod_{p\in P}p$. Every nonunit divisor remains in
$D_{\rm core}$, by decreasing $a,j$ and taking a subset
of $S$. No compatibility of original divisor phases is
assumed.

### Private points for every core class

For an original with nonempty $S$, take the full CRT point
with tag $t(a,j,|S|)$ at every $p\in S$, zero at every
palette prime outside $S$, ternary word $z_S$, and q-digit
$c_S$ if $j=1$ or 3 if $j=0$.

A rival using a prime outside $S$ misses its zero coordinate
because its tag is nonzero. A rival on a nonempty
$T\subseteq S$ can meet the point only with the same tag:
distinct tags remain distinct modulo any common palette prime.
Tag equality forces $a'=a$, $j'=j$, and $|T|=|S|$, hence
$T=S$ and the same original label. This excludes every other
nonempty-cofactor core class.

The safe word $z_S$ avoids the pure 3 and 9 guards. For
$j=0$, q-digit 3 avoids every cofactor-free q-guard. For
$j=1$, the digit is neither 0 nor 1, and if it is 2 then
$z_S\ne2$. Thus the three q-guards also miss the point.

The five classes in IG3 have private points with every
palette coordinate zero and respective $(\bmod9,q)$
coordinates

$$
(0,3),\quad(1,3),\quad(4,0),\quad(4,1),\quad(2,2).
$$

Every nonempty-cofactor class misses these points at a
nonzero tag, and direct substitution separates the five
cofactor-free guards. Consequently every core class has a
private point relative to the entire family. In particular,
no actual original is contained in another original.

### Fixed-q triples and empty movable sets

For each nonempty $S$, the actual originals
$qm_S,3qm_S,9qm_S$ all have q-digit $c_S$. Their middle
ternary root is $z_S\bmod3$ and their final word is $z_S$.
Every occupied cell therefore supplies an actual potentially
active $C_1$ triple.

At the primes for which SC468 applies, take any permitted
$R,f$ and any $c\in R$. The subset assigned to cell
$(c,f(c))$ supplies the required triple, with all three
digits in $R$ and both literal ternary tests satisfied.
Thus complete cell occupancy gives the universal fixed-q
triple condition without using whole coverage. In particular,
this applies to the $q=113$ realization below.

The phases of $m_S,qm_S,3qm_S,9qm_S$ modulo $m_S$ use
the four tags
$1+6(s-1),4+6(s-1),5+6(s-1),6+6(s-1)$ at every present
prime. They are pairwise distinct, so the within-group
separation in SC483 holds literally.

Digits 0, 1, and 2 have a cofactor-one owner. Every remaining
digit has owners with complementary, coprime cofactors.
Therefore, for the full actual owner set,

$$
\begin{gathered}
g_c=\gcd\{m_i:\rho_i\equiv c\pmod q,
                    \ d_i=3^{a_i}q^{e_i}m_i\}=1
                    \qquad(c\in\mathbb F_q),\\
D_h=\varnothing\qquad(h>1,\ h\mid W).
\end{gathered}
\tag{IG6}
$$

Any common control divisor at $c$ would divide $g_c=1$.
This conclusion does not discard owners or use separate
source choices at different digits.

## 3. An explicit 6,200-class realization

Set

$$
q=113,\qquad
P=(61,67,71,73,79,83,89,97,101,103),\qquad n=10.
\tag{IG7}
$$

There are 1,023 nonempty subsets and 511 complementary
pairs. Restrict the initial row pairs to pairs whose two
members each have at least three primes. This leaves
$511-10-45=456$ pairs. There are
$1023-10-45=968$ subsets with at least three primes, enough
to fill all 554 cells using only these subsets. All unused
subsets, including the 55 singletons and pairs, go to $(3,4)$.

The following deterministic assignment specifies the actual
phases completely. Identify a subset with its ten-bit mask
$s\in\{1,\ldots,1023\}$ in the displayed prime order.
Order the pairs $(s,1023\mathbin{\mathrm{xor}}s)$ with
$s<1023\mathbin{\mathrm{xor}}s$ and
$3\le\operatorname{popcount}(s)\le7$ by increasing $s$.
Assign the first 111 pairs in order to rows $2,\ldots,112$.
In each row assign the pair members, in that order, to the
first two allowed words in increasing order. Then visit the
remaining cells by increasing row and word, assigning the
least unused mask with at least three bits to each. Send all
remaining masks to $(3,4)$. No large CRT-period enumeration
is needed to recover the classes.

The largest tag is 60, below 61, and the core contains
$6\cdot2^{10}-1=6143$ labels. To include every odd prime
through 113, let $P_{\rm aux}$ contain the primes from 5
through 113 outside $P\cup\{113\}$. Give 5 and 7 height
two and every other auxiliary prime height one. For each
$p\in P_{\rm aux}$ add

$$
3^ap^e,\qquad 0\le a\le2,\quad1\le e\le H_p,
$$

with p-phase $(a+1)p^{e-1}\bmod p^e$. Its ternary test is
unrestricted at $a=0$, root 1 at $a=1$, and word 4 at
$a=2$. There are 17 auxiliary primes with total height 19,
so these add 57 labels, giving 6,200 in all. Every nonunit
divisor is auxiliary or is one of the pure 3 guards. The
enlarged cofactor carrier is
$W=\prod_{p\in P}p\prod_{p\in P_{\rm aux}}p^{H_p}$.

Extend each core private point with zero at every auxiliary
prime. All auxiliary classes miss it. For an auxiliary class,
take its actual p-phase, word 4 modulo 9, digit 3 modulo
113, and zero at every other nonternary prime coordinate.
A rival on another auxiliary prime misses zero. On the same
prime, different $e$ have different p-adic valuations, while
different $a$ at fixed $e$ have different nonzero leading
digits. Every nonempty palette class misses its zero
coordinate, and the five cofactor-free guards miss $(4,3)$.
This is a private point for the auxiliary class. The enlarged
family retains all core private points and leaves IG6 unchanged.

The complete CRT point with word 4 modulo 9, digit 3 modulo
113, and zero at every other prime-power coordinate is
uncovered. Each nonempty palette class requires a nonzero
tag, each auxiliary class requires a nonzero p-phase, and
all five cofactor-free guards miss $(4,3)$.

### Exact inventory and numerical scope

The construction has the following inventories:

| Quantity | Value |
| --- | ---: |
| Eligible nonunit q-cofactors | 1,023 |
| Eligible cofactors with at least two primes | 1,013 |
| Cofactors with at most two primes | $10+45=55$ |
| Allowed occupied cells | 554 |
| Core classes | 6,143 |
| Auxiliary classes | 57 |
| Total classes | 6,200 |

All 55 low-complexity cofactors have q-digit 3. At each of
the 109 digits $4,\ldots,112$, every actual q-bearing owner
has at least three cofactor primes, yet its full owner-cofactor
gcd is one. Thus numerical divisor closure does not supply
a witness with at most two cofactor primes at every bad digit.

Row 2 receives exactly four high-complexity subsets, and all
other subsets belong to $U=\{3,\ldots,112\}$. For the
SC479 classification,

$$
C_1=1019,\qquad C_{2A}=C_{2B}=C_3=0,\qquad
N_{\ge3}=968-4=964.
\tag{IG8}
$$

These values satisfy the fixed-q necessary inequalities SC480
and SC482. The 55 cofactors of support at most two are also
below the SC481 numerical envelope 39,101. The counts follow
from the explicit assignment and subset counts; they require
no claimed whole-cover realization.

The GHA11 individual-prime upper bounds are satisfied:
$H_3=H_5=H_7=2$ and every other supported odd-prime height
is one, with every odd prime through 113 present. Stronger
mixed-height conclusions are not satisfied. In particular,
35 is absent while $H_7=2$, violating the unconditional
SC457 implication at $p=5,q=7$. No assertion that 5 and 7
are opposite concentrated colors is needed for this failure.

The large-prime SC468 conditions also fail simultaneously.
At $q=101$ and $q=103$, every actual first digit of an
original bearing that prime is one of the 60 tags. There
are respectively 41 and 43 unoccupied digits, from which
one can select a permitted short set with no triple. At
$q=107$ and $q=109$, the auxiliary family has only the
three cofactor-one originals $q,3q,9q$, and hence no
nonunit-cofactor triple. These failures leave the fixed
$q=113$ conclusion intact while excluding any inference
that the example satisfies all EB1 consequences.

### Missing coverage on the same private fibre

At the explicit private point of a nonempty-cofactor
q-bearing original, vary only the first q-digit. Every
other nonempty palette class still misses: equal tags would
force the identical original, whose q-digit was changed.
Auxiliary coordinates remain zero. The pure q-guard covers
digit 0, and at most one of the 3q-guard at digit 1 or
9q-guard at digit 2 is live at the safe word. Those two
guards cannot both be live there.

Thus exactly one or two of the 112 changed-digit siblings
have an owner, and 110 or 111 are uncovered. This is a
failure of complete supply on one literal private fibre.
The construction proves only that closure, private points,
the stated numerical envelope, and fixed-q SC468 do not
imply a movable-digit entrance. Whole coverage or further
simultaneous relations can still rule out this pattern.

## 4. Grouping all q-heights by their actual cofactor

Return to one actual EB1 family in Report 388, Section 74,
with $H_3=2$, $q\in\{101,103,107,109,113\}$, and old
period $9q^GW$, where $(W,3q)=1$. A sufficient payment
test can use empty shallow numerical slots to enclose a
deep inverse that varies between control rows. Its hypothesis
concerns complete inverse hulls and is not implied by IG1--IG8.

The test reuses SC127's nested slots, SC130's actual common
congruence hull, and the per-cofactor prefix capacities in
SC186--SC189. Report 385 DP12 supplies the nested-slot
deficiency method, and
[Report 844, DM1--DM5](../600-649/844-collision-moment-needs-cofactor-packing.md#6-whole-output-classes-admit-an-exact-divisor-matching-test)
supplies the distinct-divisor-enclosure interface for one
complete output family. Here every actual original receives
at most one enclosure, fresh ternary exponents start at
three, and the q-to-ternary sum comparison runs across all
q-heights. This is a specialization of those interfaces,
not a new general Hall or sorting theorem.

Fix one code on a common geometric forest over the full
safe corridor, preserving the entire $(\bmod9,W)$ coordinate.
Its q-digit permutations may depend on the literal W-coordinate.
Keep every cofactor-one original inverse subtree protected,
including the actual q and 3q terminal leaves, their fixed
complete q-word suffixes, and the long continuing 9q inverse.
Use the continuation construction from Section 74 and carrier
$N=3^{3G+2}W$. Construct the complete original source before
choosing its owner.

For each nonunit $(3q)$-free cofactor $m$, collect all actual
originals $3^aq^em$, $1\le e\le G$, $0\le a\le2$, with
nonempty continuing inverse under this one code. Their number
is $k_m\le3G$. Each inverse is taken over the full corridor;
it is neither intersected with the deletion hole nor restricted
to a favorable control row.

Every inverse retains its own literal $m$-phase. Let $H_i$
be the largest integer in $\{0,\ldots,3G+2\}$ such that
all points of that complete inverse share one residue modulo
$3^{H_i}$. Sort these heights within the same m-group.
The sufficient condition is

$$
H_{(1)}\le\cdots\le H_{(k_m)},\qquad
\boxed{H_{(j)}\ge j+2\quad(1\le j\le k_m)}
\quad\text{for every }m>1.
\tag{AH1}
$$

Assign the jth inverse one enclosure of modulus $3^{j+2}m$,
with its actual m-phase and common ternary residue. AH1 makes
the assigned ternary modulus divide the full inverse hull,
so the enclosure contains every row piece. The labels are
distinct within a group and between different 3-free cofactors.
Their exponents are at least three, making them fresh against
retained q-free originals of ternary height at most two.
Nonunit m separates them from the protected cofactor-one
replacements. Their exponents are at most $3G+2$, so all
assigned labels divide the common carrier.

### The joint cost across all heights

The $3G$ possible old numerical weights at cofactor $m$,
in increasing order, are

$$
q,3q,9q,q^2,3q^2,9q^2,\ldots,q^G,3q^G,9q^G.
$$

The ordering uses $q>9$. At rank $j=3(e-1)+a+1$, the
fresh weight $3^{j+2}=3^{3e+a}$ has ratio
$(27/q)^e=(27/q)^{\lceil j/3\rceil}\le27/q<1$ to
the old rank-j weight $3^aq^e$. The sorted weights of any
$k_m$ actual used originals dominate the first $k_m$ weights
of this full list. Therefore, for $k_m>0$,

$$
\boxed{
\sum_{\text{new m-group}}M
\le\frac{27}{q}\sum_{\text{used old m-group}}d
<\sum_{\text{used old m-group}}d.}
\tag{AH2}
$$

When $k_m=0$, both sums are zero, and no strict inequality
is asserted for that group. AH2 does not match a new label
termwise to the original whose hull receives it. It compares
the one actual cofactor group's total across all q-heights,
without requiring individual inverses to be single progressions
before enclosure.

The unit donors and protected deep unit-cofactor originals
retain their Section 74 strict comparisons. Empty inverses
delete originals without replacement. Every output in the
complete hole has one full source and hence an original
owner. Terminal outputs are directly covered by their donors;
other outputs are covered by a protected unit-cofactor
replacement or the enclosure of their actual nonunit owner.
Retained q-free originals cover outside the hole. Thus AH1
for all groups produces one distinct odd nonunit whole cover
with $K'\le K$ and $\Sigma'<\Sigma$, which EB1 forbids.

### The equivalent prefix-capacity deficiency

The sorted condition AH1 is equivalent to

$$
\boxed{\#\{i\text{ in the same m-group}:H_i<t\}
\le t-3\qquad(3\le t\le3G+3,\ t\in\mathbb Z).}
\tag{AH3}
$$

If $l>0$ heights are below $t$, AH1 gives
$l+2\le H_{(l)}<t$, hence $l\le t-3$; the case $l=0$
is immediate. Conversely, $H_{(j)}<j+2$ violates AH3 at
$t=j+2$, where at least $j$ heights are below $t$ but
the capacity is $j-1$. Empty groups satisfy both conditions.

Consequently every such code in an actual EB1 family has
an actual nonunit cofactor and threshold violating AH3.
At $t=5$, this includes the previous obstruction from three
short shallow inverses. Other thresholds also charge deep
inverses that vary with the control row. The assertion uses
one simultaneous source, not a sum over separately selected
codes.

AH1 can hold for an owner that does not fix the switching
coordinate, provided all of its row pieces share a sufficiently
long ternary prefix and its entire cofactor group fits the
available labels. For example, if a group has no nonempty
shallow inverse and just one nonempty deep inverse of common
ternary height three, the group can use label $27m$.
Its usual deep label $3^{3e+a}m$ would not enclose that
inverse. This illustrates the sufficient criterion; it is
not a claimed inverse configuration in an EB1 family.

Confining a moved digit's geometric positions to a common
depth-three prefix guarantees height at least three for its
continuing inverses. With several owners of the same actual
cofactor, this alone is insufficient: AH3 at $t=4$ permits
at most one height-three inverse in that group. All higher
thresholds must also be satisfied. Disjoint block permutations
can form one valid row code without meeting these capacities.

The remaining requirement is a code satisfying AH1 for all
actual groups, or a whole-cover bound contradicting the
forced AH3 deficiency. Neither the fixed-q noncover nor this
sufficient payment criterion establishes either conclusion.
