[Index](../../../marked_head_profile.md) · [Complete component source](861-complementary-phase-repair-and-pair-anchor-rigidity.md#exact-deletion-hole-of-a-masked-component) · [Retained-pure repair](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#15-retained-pure-powers-reduce-the-fresh-repair-forest) · [Prefix obstruction](864-complete-color-covers-and-phase-product-obstruction.md)

# Whole-component digit stripping reduces repair to shared divisor labels

The exact common source in Report861 permits deleting an entire
moving component and replacing it by the q-digit-stripped classes
of one color. The obstruction is numerical freshness: a stripped
label can already belong to a retained original at another phase.
Those originals must be moved or their complete old union repaired.

If every displaced parent can receive ten distinct nonunit cofactor
divisors, with no divisor assigned to two parents, one common ternary
forest repairs them simultaneously. For b nonempty parents it uses
$23b+2\le25b$ fresh classes. At $|U|\ge83$, the smallest color
then gives a strict decrease in total class count. The simultaneous
divisor allocation is a sufficient condition; it has not been forced
for the actual component.

## Strip one color on the complete same source

Keep one globally count-minimal distinct odd whole cover, the period
$Q=9q^G W$ with $(W,3q)=1$, and the actual component C and full
moving digit set U of Report861 CP13. In the current branch q=113;
the additional support and height envelope gives $n=|U|\ge83$.
Let $M=|C|>0$. Choose a smallest color class $C_c$ and write

$$
k=|C_c|,\qquad nk\le M.
\tag{DS1}
$$

An original $i\in C_c$ has modulus $3^{a_i}q^{j_i}m_i$, with
$j_i\ge1$, $a_i\le2$ and $m_i>1$. Let $\rho_i$ be its
nonnegative literal residue and take $0\le c<q$. Define its stripped
class by the compatible congruences

$$
\begin{aligned}
\widehat d_i&=3^{a_i}q^{j_i-1}m_i,\\
x&\equiv\rho_i\pmod{3^{a_i}m_i},\\
x&\equiv(\rho_i-c)/q\pmod{q^{j_i-1}}.
\end{aligned}
\tag{DS2}
$$

The last quotient is integral because the original first digit is c;
at $j_i=1$ that congruence is vacuous. The non-q phases remain
literal. This is not division of the full original residue by q.
Since $d_i=q\widehat d_i$, stripped labels are injective, odd and
greater than one. Excluding all unit-cofactor first digits is what
ensures the last assertion after stripping.

The k stripped classes cover the entire component deletion hole.
For an output above its preserved base, form the source with that
same full9W base and q-coordinate $c+q t$, where t is the output's
entire q-coordinate reduced modulo $q^{G-1}$. CP13 supplies an
owner in $C_c$ for every
such complete source word. Removing the first digit gives exactly
DS2 at the original's own q-depth. This holds for every base in
$V_C$ and every output tail, including all integer lifts.

## Exact collision liability and count

Let B be the retained originals whose numerical labels equal some
$\widehat d_i$, $i\in C_c$. Put $b=|B|$. This is a set of original
labels, not a list of coincident residue classes. Injectivity gives
$b\le k$, and B is disjoint from C.

Delete $C\cup B$, insert the k stripped classes, and insert one
simultaneous repair family of r classes. Require every point in the
entire old union of B to belong either to a final retained original
or to a repair class. The repair must have distinct odd nonunit
moduli and be fresh against both the remaining original labels and
the k stripped labels. These conditions preserve whole integer
coverage: the stripped classes pay the old component hole, while
the final retained originals and repair cover every removed B point.

If N is the original count, the new count is exactly

$$
N'=N-M-b+k+r.
\tag{DS3}
$$

If $r\le25b$, then

$$
k+r\le k+25b\le25k+b<M+b
\tag{DS4}
$$

when $n\ge83$ and $k>0$, using DS1. If k is zero, then b and r
are zero, and $M>0$ still gives $N'<N$. Thus the stated simultaneous
repair contradicts global count minimality. No modulus-sum estimate
is needed. When B is empty, the empty repair suffices immediately.

The count budget does not create the repair. Separate repairs may
request the same numerical modulus with incompatible phases, which
is forbidden even if each individual request is correct.

Numerical collision does not always mean phase conflict. The old
classes $[12770]_{5\cdot113^2}$ and $[0]_{5\cdot113}$ are disjoint,
but stripping the first q-digit one from the former preserves its
phase zero modulo five and gives q-phase
$(12770-1)/113=113\equiv0\pmod{113}$. Its stripped class is exactly
the latter parent. Original comparable disjointness cannot be
transported through digit stripping. Equal complete APs can be
identified, as in the existing compatible-phase relaxation of
[Report385, section57](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#57-equal-full-residue-classes-may-be-merged-after-transport).
The present exchange conservatively includes all numerical collisions
in B and does not assume their phases differ.

## A single forest shares the pure tags

Assume B is nonempty. Write each old parent as
$h_i=3^{a_i}t_i$, where $a_i\le2$ and $(t_i,3)=1$. The cofactor
$t_i$ may include q. Suppose there are divisors

$$
e_{i,1},\ldots,e_{i,10}>1,\qquad e_{i,s}\mid t_i,
\qquad(i,s)\longmapsto e_{i,s}\text{ injective}.
\tag{DS5}
$$

Retain the actual disjoint pure 3 and pure 9 guards. Neither belongs
to C or B: the moving originals and their stripped labels all have
nonunit $(3q)$-free cofactors. The guards leave
fifteen roots modulo 27. Use the same retained-pure forest as the
existing $\tau=11$ repair: terminate eleven roots at depth three;
expand the other four into twelve roots at depth four; terminate
eleven of these; and expand the remaining root into three depth-five
leaves. Thus every safe ternary tail meets a leaf among these
$11+11+3$ leaves.

At one of the first eleven leaves use the single shared unit tag,
giving one AP of modulus 27. At one of the next eleven use the
single shared unit tag of modulus 81. These two APs are independent
of every parent cofactor phase.

For each parent i, use its ten tags $e_{i,1},\ldots,e_{i,10}$ at
the other ten depth-three leaves and the other ten depth-four
leaves. At the final three leaves use $e_{i,1},e_{i,2},e_{i,3}$.
Each tag imposes the literal old parent phase modulo that divisor;
CRT combines it with the assigned ternary leaf.

Every point in the whole old parent AP is covered by a retained
pure guard or a new class. A pure guard
covers its unsafe ternary root. At a safe root its tail reaches a
leaf; a shared unit leaf covers it directly, and every private tag
at that leaf divides the parent's cofactor and therefore accepts
its actual phase. Covering the whole cofactor phase is an allowed
enlargement of the old parent's liability.

The two shared unit labels are distinct from every private tag.
At a fixed depth, DS5 makes all private numerical labels distinct;
different depths have different ternary valuations. Every new
modulus has ternary height at least three, so it is fresh against
the old family and every stripped label. The total count is

$$
r=2+(10+10+3)b=23b+2\le25b.
\tag{DS6}
$$

Thus the verified liability is the whole old B union, with its
guard-covered part paid by the final retained originals. The fresh
packet alone is not required to cover those unsafe roots.

This is one simultaneous family. It neither aligns old cofactor
phases nor gives separate copies of the shared pure labels to
different parents.

## Hall's theorem supplies the allocation criterion

Let $D_i$ be the nonunit positive divisors of $t_i$. Replicate each
parent ten times, and connect each copy to $D_i$. The ordinary
finite Hall theorem gives DS5 exactly when

$$
\left|\bigcup_{i\in J}D_i\right|\ge10|J|
\qquad\text{for every }J\subseteq B.
\tag{DS7}
$$

Indeed a collection of replicated vertices with supporting parent
set J has at most $10|J|$ members and the same neighbor union.
Conversely taking all ten copies of J gives the displayed necessary
inequality. This directly reuses Hall's theorem.

For example, pairwise coprime $t_i$ with $\tau(t_i)\ge11$ satisfy
DS7, since their nonunit divisor sets are disjoint. This is a
restricted sufficient repair, not a property asserted of all actual
displaced parents. The individual inequalities $|D_i|\ge10$ do
not verify DS7 for larger parent sets. Likewise choosing a color
that is small in total does not prove every divisor-union inequality
for that color.

The current arithmetic obligation is to obtain such a simultaneous
allocation, or a different whole-union repair within the count
budget, from the actual common source. A failure of DS7 only rejects
this particular ten-tag construction; it does not prove that all
simultaneous repairs fail. The unrestricted covering problem remains
unsettled.

## An actual rich-parent control fails every color's Hall condition

An explicit family of 2699 distinct odd original classes has numerical
divisor closure, a private point for every original, the full 83-color
inventory and one actual masked component. Every color has two moving
owners and two displaced parents, each with twelve cofactor divisors.
Nevertheless every color fails DS7 by nine tags. A stronger counting
obstruction also excludes every finite repair using the union of those
parents' canonical divisor palettes, even with assistance from all final
retained originals and the selected stripped classes. This family is a
**NONCOVER**: it does not satisfy the complete every-color service used
in DS2. The construction and checks below are ordinary mathematical
deductions and exact finite computations, without a Lean verification
claim.

Put $q=113$, $G=10$, and let P be the eighteen primes from 37 through
109 and A the nine primes from 5 through 31. Order the pairs
$(p,s)\in P^2$, $p\ne s$, lexicographically, take the first 83,
and assign them in order to $c=30,\ldots,112$. Write
$n_c=p^5s$. Let $\mathcal D$ be the union of all nonunit positive
divisors of the $n_c$; it has 443 members. Include all six labels
$3^a q^j m$, $m\in\mathcal D$, $a=0,1,2$, $j=0,1$.
Present ternary coordinates equal four. For a singleton cofactor
$m=p^e$, its literal p-coordinate is

$$
\rho_p=(1+a+3j)p^{e-1}\pmod{p^e}.
\tag{DS8}
$$

For $m=r^\alpha s^\beta$, $r<s$, use

$$
\begin{aligned}
\rho_r&=4+a+15j+3(\beta-1)\pmod{r^\alpha},\\
\rho_s&=4+a+15j+3(\alpha-1)\pmod{s^\beta}.
\end{aligned}
\tag{DS9}
$$

The q-bearing rows $a=0,1$ on $m=n_c$ have first q-digit c.
Every other q-bearing cofactor row has first digit $3+a$.
Include the pure guards $[0]_3,[1]_9$, and all thirty unit-cofactor
labels $3^a q^j$, $a=0,1,2$, $1\le j\le10$, with q-coordinate
$3(j-1)+a$ modulo $q^j$ and present ternary coordinate four.
For each auxiliary prime $r\in A$, include $[0]_r$.
The unit originals protect exactly digits $0,\ldots,29$, leaving
the full set $U=\{30,\ldots,112\}$. The total count is
$6\cdot443+30+2+9=2699$; the complete support consists of the
27 cofactor primes through 109, together with 3 and q.

CRT fixes every original residue. The
[checker](../../../frontier/cover-geometry/shared-parent-hall-control/verify_hall_control.py)
constructs a private integer for each class using its own primary
phases, primary zero outside its support, auxiliary one, and old word
four. A q-bearing cofactor row uses q-coordinate $c+q$ modulo
$q^{10}$; a q-free row uses $30+q$. Unit originals use their own
full q-phase. Guards use their own ternary phase, and auxiliary
originals use zero at their own prime. These latter classes use
primary zero and auxiliary one elsewhere. The checker verifies each
private integer against every original and checks all 56,323
comparable numerical pairs for disjointness, as well as divisor closure.

There are exactly 166 moving owners, two on each $n_c$, with ternary
rows zero and one. Thus each numerical cofactor has only two moving
row preimages. Define the actual $E_0$ by retaining every q-free
original. Any two moving supports admit a selected pair disjoint
from their union: that union has at most four primes, whereas the
83 selected pairs have five first-coordinate centers, each with at
least fifteen partners. The bottom owner on such a pair gives a
two-edge path between the original owners. For each edge, take
their moving phases on the disjoint supports, zero at other primary
primes, auxiliary one and old word four. Moving pair phases lie
between 19 and 33; q-free pair phases lie between 4 and 18, and
q-free singleton first phases are zero or between one and three.
The point therefore lies in $E_0$. The checker verifies 951 literal
edge witnesses connecting the actual masked graph with diameter at
most two.

Every color is smallest, with $M=166$ and $k=2$. Stripping its two
owners collides with exactly the old labels $n_c$ and $3n_c$.
Their common nonternary cofactor has twelve divisors, so each parent
individually has eleven nonunit tags. For the two-parent set,

$$
|D_{n_c}\cup D_{3n_c}|=11<20=10|\{n_c,3n_c\}|.
\tag{DS10}
$$

This is a deficit of nine for all 83 colors, not just one selected
color. Individual richness, the three-row preimage bound, the full
color inventory and actual masked connectivity do not imply DS7.

The obstruction persists for the complete canonical fresh palette

$$
\mathcal P_c=\{3^k e:k\ge3,\ e\mid n_c\},
\tag{DS11}
$$

with any residue for each numerical label and at most one class per
label. Fix c. Give equal weight to the full cofactor phases of its
two old parents, put every other primary coordinate at zero and
every auxiliary coordinate at one, and fix q-coordinate $c+q$
modulo $q^{10}$. For any proposed finite packet, choose K at least
two and at least every ternary exponent in that packet, and use the
uniform ternary coordinate modulo $3^K$.

On the bottom parent's phase, the old class outside the pure guards
has ternary mass $5/9$. On the middle parent's phase its mass is
$2/9$. Thus the old-parent residual has total mass $7/18$ under
this measure. It meets no final retained original and no selected
stripped class. The checker verifies all seven relevant roots modulo
nine for each color, giving $83\cdot7=581$ checked states. This
exhausts their ternary dependence: all retained original heights
are at most two and the selected stripped heights are at most one.

The two old cofactor phases differ at the first digit of both
support primes. Consequently a class with nonunit tag $e\mid n_c$
meets at most one of the two cofactor phases, and its mass is at
most $3^{-k}/2$. A unit-tag class has mass at most $3^{-k}$.
There are eleven nonunit tags. Distinctness of numerical labels
therefore bounds the mass of every finite canonical packet by

$$
\sum_{k=3}^{\infty}\left(1+\frac{11}{2}\right)3^{-k}
=\frac{13}{36}<\frac{14}{36}=\frac7{18}.
\tag{DS12}
$$

The uncovered positive mass yields an integer residue by CRT in
the common finite period. Hence no finite packet from DS11 repairs
the whole old B union even when all final retained originals and
the selected stripped classes can assist. Packet size and depth
have no prescribed upper bounds here; the statement does not
extend to a countably infinite family of integer progressions.
It also says nothing about fresh labels using other cofactor tags.

The missing whole-cover premise is explicit. The color-30 bottom
owner has a private integer x; keeping its entire $9W$ coordinate
and replacing its q-coordinate by $66+q\pmod{q^{10}}$ gives y:

```text
x = 77779066616826342881186887604102914710321555102203694138223085888649782507009944877527572641314426
y = 95097160355723974587805009069862873350365318173023531751807994516255419682025231108511746706694301
```

Here $W$ uses the largest occurring exponent of each cofactor prime.
The preserved base lies in $V_C$, but no color-66 owner serves it,
and no original covers y. The
[result data](../../../frontier/cover-geometry/shared-parent-hall-control/result.json)
include the common period, both integers, every color's parent
labels and Hall deficit, and the retained-class checks. From the
experiment directory, `python3 verify_hall_control.py` emits these
results; optimized mode is rejected because it disables assertions.
This actual arithmetic control rejects deductions from the listed
local premises alone. It does not refute a repair theorem that uses
the complete every-color service of a genuine whole cover.

## Verification scope

A scoped transient Lean check reuses the complete masked-component
source through its concrete integer CRT coordinates. It verifies
literal first-digit stripping, coverage of the entire component
hole, injective odd nonunit stripped labels, the actual retained
collision set, and the exact count of the exchanged family.

The shared forest is checked as an actual integer AP packet. Its
labels are distinct, have ternary depth at least three and are fresh
against both original and stripped labels. The complete old B union
is covered by this packet together with the retained pure guards;
the final whole-cover theorem consumes precisely this disjunction.
Those guards are proved to remain outside both deleted sets.
The packet has $23b+2$ labels, and its actual exchange strictly
decreases count for a smallest color when $b>0$ and $n\ge26$.
For $b=0$, the empty packet and its strict count decrease are checked
separately. The parent-set Hall condition DS7 is checked equivalent
to the injective ten-tag allocation by direct use of Mathlib Hall.

The 84 checked axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`. A separate three-closure check
verifies the q=113 example in which disjoint original parent and
child become the same complete AP after stripping. These are
transient applications of existing CRT, finite-counting, Hall and
congruence results; no new Lean declaration is retained.

The dedicated pairwise-coprime example and the 2699-class control
are not included in those Lean claims. The control's retained
program and exact data have passed their arithmetic checks, and the
finite-palette mass obstruction is the ordinary argument DS12.
No simultaneous allocation is asserted for the actual whole cover.

## A typed forest lowers the simultaneous divisor demands

The ten-tag condition DS7 can be weakened by retaining each displaced
parent's actual ternary phase. Keep the disjoint pure 3 and pure 9
guards, and let B be a nonempty set of displaced parents

$$
P_i=[\rho_i]_{3^{a_i}t_i},\qquad
0\le a_i\le2,\qquad t_i>1,\qquad (t_i,3)=1.
\tag{DS13}
$$

Write $z_i=\rho_i\bmod3^{a_i}$ and
$D_i=\{e>1:e\mid t_i\}$. These are the actual old parent phases;
no phase is chosen independently of its original. The parents and
the stripped classes still have ternary height at most two.

Normalize the retained guards to $[0]_3$ and $[1]_9$. This does not
restrict their actual phases. If the original guard phases are
$\alpha\bmod3$ and $\beta\bmod9$, disjointness gives
$\alpha\not\equiv\beta\pmod3$. Choose $u\in\{-1,1\}$ with
$u(\alpha-\beta)\equiv-1\pmod3$. The integer bijection
$x\mapsto u(x-\beta)+1$ sends the guards to the stated phases,
transports every original congruence class and preserves its numerical
modulus. All phases below use this same normalization.

Use the two shared pure leaves $[8]_{27}$ and $[7]_{81}$.
The private leaves, listed by their ternary depth k, are

$$
\begin{aligned}
F_3&=\{13,16,22,25,11,14,17,20,23,26\},\\
F_4&=\{31,58,34,61,2,29,56,5,32,59\},\\
F_5&=\{4,85,166\}.
\end{aligned}
\tag{DS14}
$$

Together these leaves partition exactly the ternary tails outside
the two retained guards. Indeed, among the fifteen safe roots modulo
27, expand the four roots $2,4,5,7$ and retain the other eleven,
using root 8 for the shared pure leaf. At depth four, expand root 4,
use root 7 for the other shared pure leaf and retain the other ten.
The final expansion of root 4 gives $4,85,166$ modulo 243.

For parent i, retain only the private leaves lying in its old
ternary phase and put

$$
F_{i,k}=\{v\in F_k:v\equiv z_i\pmod{3^{a_i}}\},\qquad
 d_{i,k}=|F_{i,k}|.
\tag{DS15}
$$

Comparable-original disjointness with the retained guards leaves
exactly the eight types in the following table. The divisor demand
column is $\max_k d_{i,k}$ for one parent. The private-class count
is $\sum_k d_{i,k}$, and the cost coefficient is
$c_i=\sum_k3^k d_{i,k}$.

| Parent type $(a_i,z_i)$ | $(d_{i,3},d_{i,4},d_{i,5})$ | Individual divisor demand | Private classes | $c_i$ |
| --- | --- | ---: | ---: | ---: |
| $(0,0)$ | $(10,10,3)$ | 10 | 23 | 1809 |
| $(1,1)$ | $(4,4,3)$ | 4 | 11 | 1161 |
| $(1,2)$ | $(6,6,0)$ | 6 | 12 | 648 |
| $(2,2)$ | $(2,3,0)$ | 3 | 5 | 297 |
| $(2,4)$ | $(2,2,3)$ | 3 | 7 | 945 |
| $(2,5)$ | $(2,3,0)$ | 3 | 5 | 297 |
| $(2,7)$ | $(2,2,0)$ | 2 | 4 | 216 |
| $(2,8)$ | $(2,0,0)$ | 2 | 2 | 54 |

At each depth independently, assign a tag $e_{i,k,v}\in D_i$ to
each $v\in F_{i,k}$, requiring all tags at that depth to be distinct.
Tags may be reused at different depths. By the same finite Hall
theorem used in DS7, such assignments exist exactly when

$$
\left|\bigcup_{i\in J}D_i\right|
\ge\sum_{i\in J}d_{i,k}
\qquad\text{for every }J\subseteq B
\text{ and }k\in\{3,4,5\}.
\tag{DS16}
$$

This is Hall applied separately to the parent copies at each depth;
it does not require the same divisor assignment at different depths.
The stronger condition with right side
$\sum_{i\in J}\max_k d_{i,k}$ also suffices. For parents confined
to rows zero and one these conditions agree, since every parent's
maximum is attained at both depths three and four. DS7 implies
DS16, but DS16 demands only four or six tags for a row-one parent
and two or three for a top parent.

Given DS16, replace a private leaf v for parent i by the CRT class

$$
x\equiv v\pmod{3^k},\qquad
x\equiv\rho_i\pmod{e_{i,k,v}}.
\tag{DS17}
$$

Every point of the entire old parent $P_i$ is covered by a retained
guard, a shared pure leaf or one of its assigned private classes.
At a private leaf, its tag divides $t_i$, so the point satisfies the
literal old cofactor congruence in DS17. This verifies coverage of
the full simultaneous old parent union, including points outside
the original component deletion hole.

At a fixed depth, injectivity of the assigned tags makes the
numerical labels distinct. Different depths have different ternary
valuations, and the private tags exceed one, so they cannot collide
with the shared pure labels. All labels have ternary height at least
three and are therefore fresh against the retained originals and
the stripped classes. The common packet is one permanent assignment;
it is not a collection of incompatible parent-by-parent repairs.

## Exact count and modulus-sum payment for the typed forest

Let $E_{i,k}$ be the set of divisors assigned to parent i at depth k.
With the two shared pure leaves included once, the packet has

$$
\begin{aligned}
r&=2+\sum_{i\in B}\sum_{k=3}^{5}d_{i,k},\\
\Sigma_{\mathrm{repair}}
 &=108+\sum_{i\in B}\sum_{k=3}^{5}
       3^k\sum_{e\in E_{i,k}}e\\
 &\le108+\sum_{i\in B}c_i t_i.
\end{aligned}
\tag{DS18}
$$

The inequality uses $e\mid t_i$ and $e>0$, hence $e\le t_i$.
The preceding line is the exact sum, so an actual assignment can
use its selected divisor values instead of the upper bound. In
particular, for a purely lower-row selection, with parent counts
$b_0,b_1,b_2$ of types $(0,0),(1,1),(1,2)$,

$$
r=2+23b_0+11b_1+12b_2.
\tag{DS19}
$$

For all eight types, $r\le23|B|+2\le25|B|$. The empty-parent case
uses an empty packet, with count and cost zero.

There is a further exact cancellation when $G=1$. Let C be the
set of deleted q-bearing originals, $M=|C|$, and let S be a selected
subset whose literal q-strips cover the entire hole left by deleting
C. This coverage is a premise of the exchange: DS2 supplies it for
one complete color of a component, and Report864 PC66 supplies it
for the fixed lower selector when C consists of all q-bearing
originals. These two choices have different size guarantees.

Every selected original has label $q h_i$, where
$h_i=3^{a_i}t_i$, $a_i\le2$, $t_i>1$ and $(t_i,3q)=1$,
as in DS13. Thus no stripped label is either retained pure guard.
Divisor closure supplies the unique actual original
with label $h_i$. It is q-free, hence outside C. The strips have
distinct labels, so their entire collision set B has $|B|=|S|$,
and the sums of the numerical labels of B and of the strips are
equal. Delete C and B, insert the strips and one fresh simultaneous
repair of B as above. If N and $\Sigma$ are the original count and
modulus sum, then

$$
N'=N-M+r,\qquad
\Sigma'=\Sigma-\sum_{i\in C}\operatorname{modulus}(i)
                    +\Sigma_{\mathrm{repair}}.
\tag{DS20}
$$

Thus $r<M$ gives a count contradiction. If $r=M$, a strict
inequality between the repair sum and the deleted C sum gives
the secondary contradiction when the original cover is also
modulus-sum minimal among count-minimal covers. The cancellation uses
numerical labels, not equality of old and inserted phases.

For a smallest complete color, write $k=|S|$. DS1 gives
$nk\le M$, and DS18 gives $r\le25k<M$ when $n\ge26$ and
$k>0$; if $k=0$, the empty repair suffices. This count comparison
needs no modulus-sum estimate. The fixed union of lower owners in
Report864 PC66--PC68 is not one smallest complete color and does
not inherit $nk\le M$. Its parent repair must instead be compared
with its actual deleted count using DS20.

## What the typed condition leaves unresolved

DS16 is a sufficient simultaneous repair criterion. Neither the
fixed two-owner selector nor its pointwise lower-color multiplicity
has been shown to force this criterion in the actual whole source.
For a prime cofactor $t_i=p$, the only nonunit divisor is p, whereas
every row in the table needs at least two distinct divisors. Such
a parent fails even the singleton instance of DS16. The pointwise
lower-color bound 32 in Report864 PC65 does not by itself discard
these parents: 27 cofactor-prime axes provide 54 possible numerical
lower labels $qp,3qp$. This inventory comparison is not an assertion
that a whole cover realizing such service exists.

Failure of DS16 rejects this particular whole-parent forest, not
every possible repair. Other final retained originals and the inserted
strips can reduce the actual parent liability; compatible old cofactor
phases can permit a class to serve several parents; and tags outside
the displayed divisor palettes are not excluded by this test. A
bridge from the actual shared source to a feasible permanent plan,
with its complete deletion liability and payment, remains unproved.

A scoped Lean check verifies the exact partition on all 243 ternary
words, the eight rows of private-leaf counts and every displayed
cost coefficient. Its three checked declarations have empty axiom
closures. These finite checks do not prove DS16 for the actual
parents. The conditional Hall, CRT and exchange arguments above
reuse the existing interfaces; no new D5 declaration or actual-source
closure claim is made.
