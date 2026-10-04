[Index](../../../marked_head_profile.md) · [Actual component source](861-complementary-phase-repair-and-pair-anchor-rigidity.md#exact-deletion-hole-of-a-masked-component) · [Different local control](862-three-support-masked-rectangle-control.md) · [Colorful Helly source](../../../../../../Library/Combinatorics/pohoata2025colorfulhelly.md)

# Complete color covers can still obstruct fresh prefix replacement

There is a prescribed arithmetic mask with 83 complete color covers,
all five top-word cells in every color, and edgeless top prime-phase
collision graphs, for which a fresh replacement using at most one
AP per original and preserving each literal cofactor needs at least
135 colors. This obstruction permits arbitrary new ternary depths
and does not need a modulus-sum constraint.

The mask is not the complete hole of its retained arithmetic family.
The construction also uses 83 cofactor primes, exceeding the separate
27-prime envelope in the current q=113 branch. It is a control against
a theorem using only the prescribed-mask color covers and those local
incidences. It is not a model of the complete EB1 hypotheses or a
counterexample to Erdős #7.

Unlike Report862, every color covers this entire prescribed mask and
every higher q-suffix. The additional obstruction is the absence of
mixed whole subcovers on a Cartesian phase source.

## One literal phase product

Take q=113, $U=\{30,\ldots,112\}$, $n=83$, and

$$
(u_1,u_2,u_3,u_4,u_5)=(2,4,5,7,8),\qquad
W=\prod_{c\in U}p_c^5,
\tag{PC1}
$$

where the $p_c>113$ are distinct primes. For $a\in\{0,1,2\}$ and
$1\le h\le5$, set $s_{a,h}=3(h-1)+a+1$. These fifteen small
integers are distinct already modulo every $p_c$.

The moving original $(c,a,h)$ is the CRT class

$$
d_{c,a,h}=3^a q p_c^h,\qquad
x\equiv c\pmod q,\quad
x\equiv u_h\pmod{3^a},\quad
x\equiv s_{a,h}\pmod{p_c^h}.
\tag{PC2}
$$

For a safe old word u, write

$$
D(u)=\{(a,h):u\equiv u_h\pmod{3^a}\},\qquad
T(u)=\{s_{a,h}:(a,h)\in D(u)\}.
\tag{PC3}
$$

Define the common mask on the preserved old-word/cofactor carrier by

$$
M=\{(u,w):u\in\{2,4,5,7,8\},\quad
            w\bmod p_c^5\in T(u)\text{ for every }c\in U\}.
\tag{PC4}
$$

For fixed $(u,w)\in M$ and color c, exactly one $(a,h)\in D(u)$
has $w\bmod p_c^5=s_{a,h}$. Every other same-color original misses
already at the first $p_c$-digit. Thus the masked supports of each
color partition the same entire M. All moving originals have q-height
one, so this is also coverage of every higher q-suffix with first
digit c. Each base has exactly n active moving supports, one of each
color.

Every color has a top original at each of the five words. The masked
support graph is connected: bottom owners span all safe old words,
and owners of different colors at a common allowed word intersect
by independent choices of their cofactor coordinates. A bottom owner
of another color connects two owners of one color, including when
their permitted word sets differ.

## A retained label bank makes freshness literal

For each $(c,a,h)$ retain the q-free original of numerical label
$3^a p_c^h$, ternary phase $u_h\bmod3^a$, and cofactor phase
$16+3(h-1)+a$. Also retain $[0]_3$, $[1]_9$, and the thirty
unit-cofactor originals

$$
3^a q^j,\qquad 0\le a\le2,\quad1\le j\le10,
\qquad\text{first q-digit }3(j-1)+a.
\tag{PC5}
$$

Their higher q-digits are zero and their ternary coordinates, when
present, equal four. This bank misses M at moving first digits.
Its unit-cofactor digit complement is exactly U and its largest
q-height is ten.

All numerical labels are distinct odd nonunits and divisor-closed
above one. Comparable originals are disjoint. In one cofactor axis,
different $(a,h)$ use different first-prime phases; moving and
retained cofactor phases lie in disjoint bands 1--15 and 16--30.
Different moving colors have distinct q-digits and distinct cofactor
primes. The unit-cofactor first digits are distinct and outside U.
The safe ternary choices separate every relevant class from the pure
3 and pure 9 originals.

Private integers can be chosen by CRT. For a moving or retained
cofactor class, choose its cofactor phase, set all other cofactor
coordinates to zero, and use its safe word; choose its moving
q-digit in the former case and a digit in U in the latter. For a
unit-cofactor class use its own q-digits, old word four and all
cofactor coordinates zero. The pure guards have private words zero
and one with a q-digit in U and all cofactor coordinates zero.

Every original has at most two nonternary support primes. The
four-of-five phase tests are therefore empty. At a fixed old word,
no two top originals agree at two common nonternary primes, including
retained originals, so every GLC1 collision graph is edgeless.

These checks do not identify M with the actual complete hole $E_0$.
An old safe word with all cofactor coordinates zero lies in $E_0$
but not M. With a first q-digit in U it is also uncovered by every
moving original. The full arithmetic family is a NONCOVER, and M
is not asserted to be its actual component union $V_C$.

## Whole coverage requires completion of a color

Delete the moving originals while retaining the label bank. Allow
each moving original at most one new AP, preserving its exact
cofactor $p_c^h$ and phase $s_{a,h}$. The new numerical modulus is
$3^{k_{c,a,h}}p_c^h$; no q-factor is retained in this replacement
class. The ternary prefix can be chosen arbitrarily and originals
may be left unused.

Freshness against the bank forces $k_{c,a,h}\ge3$. For fixed
$(c,h)$, numerical distinctness forces the three used exponents for
$a=0,1,2$ to be different. Let $P_{c,a,h}$ be the chosen ternary
prefix cylinder, or the empty set for an unused original. Work on
a common ternary period $3^L$, with L at least five and at least
every used prefix depth.

For a complete ternary word z above old word u, the new family
covers every cofactor point of M above that word if and only if

$$
\exists c\in U\quad z\in\bigcap_{(a,h)\in D(u)}P_{c,a,h}.
\tag{PC6}
$$

One completed color suffices because it covers all of M. Conversely,
if every color has an inactive required prefix, choose one such
pair $(a_c,h_c)\in D(u)$ for each c. Choose the single simultaneous
CRT point

$$
w\bmod p_c^5=s_{a_c,h_c}\quad(c\in U).
\tag{PC7}
$$

It belongs to M. Its only possible replacement of color c has the
chosen inactive prefix, and every other replacement of that color
misses modulo $p_c$. This one point is missed by the entire new
family. No independent private witnesses are substituted for a
common missed source.

## The sharp 135-color threshold

Let $J_c(u)$ be the set of ternary words above u belonging to every
prefix required in PC6. The bottom pair $(0,1)$ belongs to every
$D(u)$. Its one fresh prefix fixes an old word, so a color has
nonempty $J_c(u)$ for at most one safe u.

For u equal to $u_h$, all three $(0,h),(1,h),(2,h)$ are required.
If their prefixes have a common point, all three were used. Their
distinct exponents are at least three, so the largest is at least
five. Hence the complete-color region lies inside one depth-five
ternary cylinder. On the common period,

$$
\left|\bigcup_u J_c(u)\right|\le3^{L-5}.
\tag{PC8}
$$

PC6 requires these regions to cover all $5\cdot3^{L-2}$ safe
ternary words. Counting their union gives

$$
5\cdot3^{L-2}\le n\,3^{L-5},\qquad n\ge135.
\tag{PC9}
$$

Thus n=83 is impossible in this replacement class, even before
checking the modulus-sum price.

Sharpness concerns the prescribed patch, not the full available
digit complement. Take q=167 and choose 135 moving colors from
$\{30,\ldots,166\}$, using one distinct cofactor prime greater
than q for each color. Use the same mask and bank construction on
those colors. There are 135 depth-five cylinders above the five safe
old words. Assign one color to each cylinder, represented by
$v_c\bmod243$, and use

$$
x\equiv v_c\pmod{3^{3+a}},\qquad
x\equiv s_{a,h}\pmod{p_c^h}.
\tag{PC10}
$$

For every output tail, its assigned color covers every compatible
cofactor point. All new labels are distinct and fresh. There is one
replacement per original and each modulus is multiplied by $27/q$,
so the patch repair preserves count and strictly reduces its modulus
sum. These 135 colors are a subset of the 137 digits outside the
thirty protected first digits; no full-complement claim is made.

## A different literature invariant for mixed subcovers

Pohoata--Yang--Zhang, *Colorful Helly via induced matchings*,
[arXiv:2501.17149v2, Theorem 1.3](https://arxiv.org/html/2501.17149v2#S1.Thmtheorem3),
can be applied directly to complements of original supports on one
common source X. Its condition bounds the largest r for which
selected supports $S_{i_1},\ldots,S_{i_r}$ have respective private
points $x_1,\ldots,x_r$ and a point $x_0$ missed by all of them:

$$
x_s\in S_{i_t}\iff s=t,\qquad
x_0\notin\bigcup_{t=1}^r S_{i_t}.
\tag{PC11}
$$

A bound $\tau'\le82$ for that parameter would extract a whole
rainbow subcover from 83 complete color covers. No such bound is
established on the actual masked component, and a rainbow subcover
alone supplies neither prefix compatibility nor numerical payment.

The product control separates this invariant from GLC1. At u=2,
each color has nine pieces: five bottom, three middle and one top.
Choose eight, omitting one fixed bottom piece. Give each selected
piece its own phase in its own color coordinate and the omitted
phase in every other coordinate. These are private points relative
to all $8n$ selected supports. The point with all omitted phases is
missed by all of them. Thus this source has $\tau'\ge8n=664$
although every top prime-phase collision graph is edgeless.

On each fixed-word phase product, a union of selected pieces covers
the whole source only if some selected color covers it alone; this
is PC6 without the prefix notation. Beating that completed-color
constraint in the actual arithmetic problem requires information
not supplied by the abstract color-cover identity. Two actual
conditions absent from this control are the exact retained-family
origin of $E_0$ and the 27-prime envelope. Neither is proved here
to force a mixed subcover or a paid replacement. Changing cofactors,
retaining q-factors or using explicitly paid additional donors also
falls outside the obstructed replacement class.

## Verification scope

A scoped transient Lean check proves the Cartesian common-missed-point
equivalence PC6 and the prefix/count obstruction PC8--PC9. Prefixes
use actual natural-number congruences. From used depths at least
three and pairwise distinct used depths for each same-cofactor
triple, it derives that a completed color occupies at most one
depth-five cylinder; this capacity is not an assumed premise.
Counting on $(\mathrm{Fin}\,9\times\mathrm{Fin}\,27)
\times\mathrm{Fin}(3^t)$ then gives $135\le n$ and the explicit
83-color contradiction for old words $(2,4,5,7,8)$.

The nine checked axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`. These are transient applications
of the pinned choice, congruence and finite-counting results; no new
Lean declaration is retained. The literal integer bank and its
freshness-to-depth implication, its CRT identification with the
phase product, the q=167 sharpness construction and price, and the
$\tau'\ge664$ example remain ordinary deductions in this scope.
The cited colorful Helly theorem is reused from its primary text;
it is not claimed as a new Lean result.
