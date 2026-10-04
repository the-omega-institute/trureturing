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
