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

## Original private points restrict the small-Helly branch

Return to a genuine whole cover and its actual component C from
Report861. Keep all original private points. Normalize each color's
supports by stripping its first q-digit, on the same source

$$
X_C=V_C\times\mathbb Z/q^{G-1}\mathbb Z,
\qquad k_c=|C_c|.
\tag{PC12}
$$

Every color covers all of this source. It is also irredundant there.
For an original i of color c, take its global private integer. Its
base avoids every q-free original and belongs to $F_i$, hence to
$V_C$. Removing the first q-digit gives a point in its stripped
support. If another original of the same color contained that
normalized point, restoring the first digit c would put the original
private integer in both original classes. Thus each stripped support
has a private point relative to its entire color.

Omit one support from a color. Its private point is missed by all
the remaining $k_c-1$ supports, and their own private points still
witness PC11. Consequently the comatching parameter of all the
normalized supports satisfies

$$
\tau'(X_C)\ge k_c-1\qquad\text{for every }c\in U.
\tag{PC13}
$$

This argument uses one color at a time. Private points of different
original q-colors need not remain private after their first digits
are removed; PC13 is not a lower bound of $M-1$ from all M owners.
In particular the proposed sufficient bound $\tau'\le82$ requires
every color to have at most 83 owners, not merely a small average or
one smallest color.

There is a further source consequence. Suppose an original i of
color c has q-height at least two, and fix the base of its global
private point. No q-height-one original of that color is active at
this base: it would cover the private point. Complete color service
requires an owner for each of the q possible next digits, with all
later digits fixed. Every active owner has q-height at least two
and can accept only one next digit. Selecting an owner for each
digit is therefore injective, so

$$
\text{some }i\in C_c\text{ has }j_i\ge2
\quad\Longrightarrow\quad k_c\ge q.
\tag{PC14}
$$

For q=113, PC13--PC14 show that $\tau'\le82$ can hold only when
every moving original of C has q-height one. The actual parameter
bound has not been proved. Its failure excludes this particular
Helly certificate, not the existence of a rainbow subcover or a
different paid exchange.

Divisor closure makes the remaining height-one case particularly
explicit. Every stripped label $3^{a_i}m_i>1$ already belongs to a
q-free original, which is retained outside C. Its old phase differs
from the stripped phase: equality would make the original q-bearing
child contained in that parent, contradicting its private point.
Stripping is injective on numerical labels, so the collision set of
[Report865](865-whole-component-digit-stripping-and-shared-parent-repairs.md)
then satisfies

$$
b_c=k_c,\qquad N'=N-M+r_c.
\tag{PC15}
$$

Thus the old-parent repair must still fit $r_c<M$. Those q-free
parent classes lie outside $E_0$. A rainbow cover of $X_C$ does not
by itself establish coverage of their deletion liability or authorize
assigning two phases to the same numerical label. This identifies the remaining
arithmetic obligation even in the branch where the small Helly
certificate could apply.

## Coloring by fresh moduli has its own partition obstruction

One could instead choose a finite nonempty set of fresh numerical
moduli $\mathcal M$ in advance and let color m contain its permitted phase traces
$X\cap[a]_m$ on one common nonempty residual X. If each such color
covers all of X and its comatching parameter is at most
$|\mathcal M|-1$, the cited theorem directly chooses one phase per
modulus covering X. Numerical distinctness is then built into the
colors, although the chosen label count must still fit the budget.

This sufficient condition need not certify even an existing repair.
For fixed m, its nonempty phase traces partition X. Write
$r_m=|\operatorname{image}(X\bmod m)|$. Choose one point in each
of $r_m-1$ cells and a common missed point in the remaining cell.
These cells satisfy PC11, so

$$
\tau'\ge r_m-1\qquad(m\in\mathcal M).
\tag{PC16}
$$

Hence this certificate requires $r_m\le|\mathcal M|$ for every
chosen m. Pruning phases while requiring that color to cover all X
cannot remove any nonempty cell of its partition.

For example, consider the complete safe cofactor corridor of one
bottom parent,

$$
X=\{x\in\mathbb Z:x\equiv\rho\pmod n,
       \ x\not\equiv a\pmod3,\ x\not\equiv b\pmod9\},
\qquad (n,3)=1,\quad b\not\equiv a\pmod3.
\tag{PC17}
$$

For $e\mid n$ and $k\ge2$, CRT realizes every safe ternary root
with the fixed cofactor phase, giving

$$
|\operatorname{image}(X\bmod3^k e)|=5\cdot3^{k-2}.
\tag{PC18}
$$

When $\tau(n)=11$, the existing retained-pure repair of Report385,
section15, covers this entire corridor with 25 distinct labels:
eleven at ternary depth three, eleven at depth four and three at
depth five. For any depth-five label $243e$, PC18 gives 135 phase
cells. Thus the full phase-family parameter is at least 134, which
fails the proposed threshold 24 despite the existing 25-label
repair. A depth-four label already has 45 cells.

This is a limitation of the sufficient Helly condition on this
specified corridor. An actual expanded residual can be smaller
after other retained and stripped classes receive credit; neither
135 nor the resulting obstruction may be transferred to that
smaller source without checking its actual phase cells. A phase
family that omits required cells also loses the complete-color
premise. Both uses of the literature theorem must preserve the
same residual source and its full color covers.

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

A further scoped transient check verifies the actual integer-to-common-
source transport in PC12--PC14. Original global private integers yield
same-color private points, omitting one owner produces the private-point
and common-miss witness, and the q next-digit suppliers form an actual
injection into the color. Given an explicit upper bound T on these
comatching witnesses and $T+1<q$, it concludes that every component
original has q-height one.
Given the actual q-free parent at each stripped label, it also verifies
the parent's collision membership, different phase and exclusion from
$E_0$, and proves $b_c=k_c$. Extracting those parent indices from the
ordinary divisor-closure premise is not included in this check.

The general partition witness in PC16 is checked. For PC17--PC18, the
same compilation checks the concrete corridor $n=5^{10}$, $\rho=0$,
with pure guards zero modulo three and one modulo nine. Its phase
range modulo $1215=243\cdot5$ is proved equal to a finite set of
cardinality 135: each phase has an actual CRT integer in the corridor,
and every corridor integer has one of those phases. It constructs the
134-support private-point/common-miss witness. The existing repair is
instantiated as 25 distinct odd nonunit labels, including 1215, and
is proved to cover the whole parent together with the guards. Thus
the mismatch between a valid repair and this Helly sufficient
condition uses actual congruence classes, not an assumed phase count.

These 110 checked axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`. They remain transient reuse
checks, with no retained new Lean declarations. The arbitrary-parameter
cardinality formula PC18 remains an ordinary CRT deduction. Neither
check proves the small comatching bound for the actual component,
supplies its simultaneous parent repair, or resolves the unrestricted
odd covering problem.

## A prime-coordinate bound allows one omission from every color

The PC6 product obstruction has a limitation when all supports are
literal congruences on a carrier with few distinct prime factors.
Let N>0, let X be any subset of the integers, and let n finite indexed
families of congruence classes each cover all of this same X. Every
modulus is positive and divides N. In each color choose two distinct
indices that are allowed to be omitted. If

$$
n>\omega(N),
\tag{PC19}
$$

one can omit one of those two indices from every color while keeping
the union of all remaining classes a cover of X. This does not mean
retaining only one class per color. The sets and their phases stay
fixed, and X need not be a product or have positive prescribed density.

Here is an explicit one-switch proof. Start by omitting the first
chosen class A_c in every color. If the remaining union covers X,
there is nothing to change. Otherwise choose a missed point x_0.
Since each color is a complete cover, its omitted class is its only
class containing x_0. In particular

$$
A_c=[x_0]_{m_c}.
$$

Some m_c divides the lcm of all the other selected moduli. Indeed,
otherwise every color would have a prime at which its modulus has
strictly larger valuation than every other selected modulus. Such
primes are distinct and all divide N, contradicting PC19. This is
the usual breadth bound for the divisor lattice, whose coordinates
are the prime-exponent chains.

For this c restore A_c and omit the second permitted indexed class
instead. Any point y missed by the new union would belong to A_d
for every d different from c, by completeness of those colors. It
would therefore be congruent to x_0 modulo their lcm, hence modulo
m_c. But A_c has been restored, a contradiction. Thus from any
initial omission selection, either it already works or changing
the omission in just one color makes it work.

Repeated supports, empty traces on X and the modulus one cause no
failure of the argument. N>0 and two distinct available indices per
color are essential to this formulation. The bound counts distinct
prime factors, not their multiplicities. It is sharp at n=omega(N):
for a squarefree N and X equal to the entire integer source, give
one color all residue classes modulo each
prime divisor. Every omission selection then has a common missed
point by CRT.

If each color family has first been reduced to an inclusion-minimal
cover and has at least two members, every omitted member has a
private point within that family. Consequently the remaining part
of each individual color fails to cover X, although their union
covers X. This is an actual mixed subcover, in the precise sense

$$
X\subseteq\bigcup_c\bigcup\mathcal R_c,
\qquad
X\nsubseteq\bigcup\mathcal R_c\quad\text{for each }c,
\tag{PC20}
$$

where R_c is its fixed minimal cover with one member removed.
Passing to minimal covers is needed for the second assertion:
merely deleting a nonempty but redundant support would not prove it.

The lattice-breadth ingredient is classical. Baker--Stralka,
[*Compact, distributive lattices of finite breadth*](https://doi.org/10.2140/pjm.1970.34.311),
Pacific Journal of Mathematics 34 (1970), Section 2, recalls the
meet-irredundancy definition and its product-of-chains setting.
The concrete divisor-lattice bound here follows directly from
prime valuations. There is also a direct application of
Pohoata--Yang--Zhang, Theorem 1.3, to the common unique-owner locus

$$
Y=\{x\in X:\text{each color has exactly one indexed owner at }x\}.
$$

For every omission plan o, writing R(o) for its retained union gives

$$
X\setminus R(o)=Y\cap\bigcap_c A_{c,o(c)}.
\tag{PC24}
$$

Different indexed owners of one color have disjoint traces on Y.
Repeated equal supports have empty traces there. A comatching with
common point for the family of these traces uses only points in Y,
so it supplies actual AP membership and nonmembership witnesses.
The same prime-valuation argument bounds its parameter by omega(N).
The cited theorem therefore chooses one omitted trace per color
with empty intersection, and PC24 proves PC19's existence conclusion.
This uses neither the complement application that retains only one
support per color nor an owner's individual private region. The
stronger one-switch assertion follows from the direct argument above.
Both are reuse-based deductions, with no originality claim.

## The exact old-word source has enough genuinely mixed colors

Return to one actual EB1-minimal distinct odd whole cover with H_3=2
and q=113. Reuse Report850 CD87 to obtain G=1. Report388 SC439--SC440
gives P^+(Q)<=113, so with Q=9qW and (W,3q)=1,

$$
\omega(W)\le27.
\tag{PC21}
$$

The 27 possible cofactor primes are the odd primes at most 113 other
than 3 and 113. Higher powers do not increase this count. Let U
exclude all the actual q,3q,9q digits; |U|>=110. Fix any actual safe
old word z modulo nine, and let X_z be the exact q-free residual
on that word's full W carrier. For every c in U, all the actual
q-stripped originals of color c cover this same entire X_z. This
uses G=1 and actual whole coverage; all cofactor phases are literal.

SC468 with the constant assignment f=z implies that at most five
colors in U lack a top original whose old word is z. Otherwise
six such colors would contradict its required divisor triple.
Thus at least 105 distinct top originals have this word. Each has
a private original point; its cofactor lies in X_z, making X_z
nonempty. These facts concern the exact retained-family residual,
not the prescribed product mask of PC4.

### Two different enclosing cofactors would pay a complete deletion

Suppose X_z were contained in both [r_1]_{s_1} and [r_2]_{s_2},
where s_1,s_2 are different nonunit divisors of W. Delete every
q-bearing top original with old word z, retaining all other originals.
At least 105 originals are deleted. A point in the complete joint
deletion hole must have old word z: original coverage supplies a
deleted owner. It also avoids every q-free original, all of which
were retained, so its cofactor belongs to X_z. No union of separate
private regions has replaced this joint hole.

Take the three fresh numerical labels

$$
27,\qquad 27s_1,\qquad 27s_2.
\tag{PC22}
$$

Their ternary residues are z,z+9,z+18 modulo 27 respectively, using
0<=z<9. The last two retain r_1 modulo s_1 and r_2 modulo s_2;
CRT supplies their complete AP phases. Every point of the hole
satisfies both cofactor tests, and its next ternary digit selects
one of the three repairs. All integer lifts are covered.
The labels are distinct odd nonunits, and their ternary height
three makes them fresh against all retained originals. Replacing
at least 105 classes by three contradicts class-count minimality.

This is precisely the existing Report385 DR7/NF4 three-child hull
repair applied to a complete simultaneous deletion. It is not a new
generic exchange theorem. In particular the full cofactor hull of
X_z can only be one or a single prime: any composite hull divisor
would supply two different nonunit divisors for PC22.

### Minimal color covers have at least two members in almost every color

If one actual stripped owner of a color in U covers all X_z, its
cofactor is nonunit because all unit-cofactor digits were excluded.
By the preceding argument all such whole-source owners, across all
colors and all three rows, must have the same cofactor s. There
are at most three of them, since the only possible original labels
are qs,3qs,9qs and numerical labels are distinct. Therefore at
least |U|-3>=107 colors admit no single-owner cover of X_z.

Choose any 28 of these colors. In each, fix an inclusion-minimal
subcover of X_z. Each has at least two members; all its retained
supports are nonempty and have private points relative to that
color's subcover. On the fixed word z their supports are congruence
classes modulo divisors of W, restricted to the same X_z. Apply
PC19 with N=W and n=28. It yields PC20 on this very same word,
with every remaining single-color family incomplete. Thus the
universal no-mixed-subcover property of the PC6 phase product cannot
hold for these actual selected colors on the exact EB1 residual.

This excludes that particular product obstruction under the stated
whole-source and support assumptions. It does not assign new ternary
prefixes to the mixed classes, give them fresh distinct numerical
labels, or install one permanent owner per cofactor. The mixed union
can still include all three owners of some cofactor, which is exactly
where the shallow payment conflict remains. Nor does its existence
give a useful lower bound on the mass of X_z or a Cross-free point
in a specified top original's private projection.

There is also an exact distinction between the one-switch mechanism
and single-output payment. Its redundant modulus satisfies
\(m_c\mid\operatorname{lcm}_{d\ne c}m_d\), so its class contains
the common intersection of the other selected classes. This need
not contain any one of those whole classes. For example,

$$
[0]_{55}\cap[0]_{77}\subseteq[0]_{35},\qquad
[0]_{55}\nsubseteq[0]_{35},\qquad
[0]_{77}\nsubseteq[0]_{35}.
\tag{PC23}
$$

The integers 55 and 77 witness the last two failures. All three
cofactors are odd and coprime to three. This elementary distinction
is a boundary of the proposed implication, not an EB1 model.
Once other outputs are already legally paid, an intersection can
describe their remaining joint hole and enter Report858's residual
hull test. Before that payment is supplied it cannot replace the
whole inverse in the donor-containment requirement. Removing one
owner per color also need not remove every owner that forces that
color's deepest prefix, so PC19 supplies no automatic saving of
22 leaves in the 135-versus-113 comparison.

### Exact formal checks and remaining bridge

A transient Lean application proves PC19's one-switch conclusion
from the full integer congruence families, the common arbitrary X,
positive common period and chosen omission pairs. It also proves
PC20 when the individual families' private-witness condition is
supplied. Its prime-coordinate injection reuses pinned Mathlib
factorization and finite-cardinality results. It does not assume
that X is a product or substitute different sources for different
colors. All five axiom reports use only the standard three axioms.

A separate transient check constructs the PC22 CRT repair, proves
coverage of all integers, and produces an odd distinct covering system
with strictly fewer classes. Its consumer derives the complete-hole
enclosure from actual whole coverage, a deleted family of more than
three q-bearing old-word-z originals, and the two enclosures of the
exact q-free residual on that word. The consumer does not assume the
deletion hole equals a union of individual private regions. All three
axiom reports use only the standard three axioms. The SC468 color
counts, their combination with the exact X_z inputs, and the
minimal-subcover selection in the complete application remain the
ordinary reuse argument above; this is not a kernel replay of the
full EB1-to-PC20 chain. No new D5 wrapper, freeze, source-density
estimate or payment certificate is claimed.

The universal containment and two integer witnesses in PC23 have a
separate transient Lean check. It uses the ordinary coprime-modulus
combination and exact arithmetic, without asserting an original
whole-cover realization.

The exact set identity PC24, the disjointness of different indexed
traces, empty repeated traces, empty palette intersection and lifting
of the common-carrier comatching have a separate transient Lean
check. It introduces no axiom asserting the external PYY theorem.
The first four checks use only the standard three axioms; the last
is axiom-free. The external theorem is reused from its primary text.

## A mixed cover can avoid 26 prescribed cofactor blocks

The preceding fixed-word result also supplies complete colors on the
full retained-family residual

$$
E_0=(\mathbb Z/9W\mathbb Z)\setminus
       \bigcup\{\text{all actual q-free originals}\}.
$$

Choose the same at least 107 colors that require two or more owners
on one fixed X_z. Each color's full stripped family covers all E_0
and has at least two members. Its original private integers give
private points relative to its entire color after removing the
first q-digit, as in PC12. Thus these full E_0 covers are essential.
This does not claim essentiality for their traces on the fixed X_z.

Let T be any set of at most 26 nonunit divisors of W. Exclude every
moving owner with cofactor in T, that is, every present label among
qt,3qt,9qt for t in T. Since G=1 and H_3=2, distinctness gives at
most three owners per cofactor. They touch at most 78 of the chosen
colors. At least 29 untouched complete colors therefore remain, and

$$
29>\omega(9W)\quad\text{since}\quad\omega(9W)\le28.
\tag{PC25}
$$

Apply PC19 to any 29 of these untouched colors, allowing two actual
owners in each as the omission alternatives. Their retained union
covers every point of the same E_0. Each retained individual color
fails because its omitted owner has a private point. The remaining
colors need not be used. Thus one genuinely mixed cover of E_0 can
avoid all the prescribed moving owners, with their literal phases
and indexed provenance unchanged.

This is a direct consumer of PC19 and the existing whole-source
and numerical-label counts. Avoiding those blocks alone would need
only one untouched complete color; the additional assertion is that
no retained single color is complete. The excluded moving owners
do not release any of the retained q-free parent labels. Removing
parents would enlarge E_0, and coverage of that enlarged complete
hole is not established by PC25. Nor does this selection bound the
number of retained owners in every other cofactor block or assign
their fresh ternary prefixes. The remaining payment obligation is
unchanged.

A transient application of the already checked omission theorem
restricts its color type to the untouched colors. It verifies the
general condition \(\omega(N)+|B|<|C|\), the resulting whole-source
mixed cover, and the arithmetic \(28+3\cdot26<107\). Its axiom
closure uses only the standard three. The actual EB1 suppliers of
the 107 colors, their privacy, the three-owner block count and the
28-prime bound are the ordinary applications specified above; this
is not a kernel replay of that entire supplier chain.

## Cofactor projection does not preserve prefix service

Even a mixed cover using at most two owners per cofactor would
need an additional prefix condition. Consider the finite control
W=5 and the common cofactor trace X_z={0} above z=2 modulo nine.
Give three colors one owner each, all with cofactor phase zero,
on the short leaves

$$
2,\quad11,\quad20\pmod{81}.
\tag{PC26}
$$

Each color covers the entire cofactor trace. Keeping any one owner
already gives a cofactor-projected cover, using only one owner at
that cofactor. But the three leaves have different parents modulo
27. Two outputs at the fresh labels 135=27*5 and 405=81*5 can
serve at most two of those parents, leaving a required inverse
uncovered. If they enclose selected owners i and j, their phases
are forced modulo their respective output moduli. The points

$$
x_0=245,\qquad x_1=335,\qquad x_2=20
\tag{PC27}
$$

all have cofactor phase zero and old word two, and lie respectively
in the three leaves. For every i,j, including equal choices, an
index k different from both supplies

$$
x_k\not\equiv x_i\pmod{135},\qquad
x_k\not\equiv x_j\pmod{405}.
$$

Reduction modulo 27 proves both exclusions. A transient Lean check
verifies the common trace, the parent separation and this missed
integer for every i,j. Its five axiom closures use only the standard
three. The control has no original whole-cover or EB1 realization;
it refutes only the inference from cofactor-projected coverage
(even with one selected owner per cofactor) to payment in this
fixed geometry. Each color in this control is already complete,
so the control itself does not satisfy PC20's genuinely mixed
condition.

For the actual geometry, Report858 SF2--SF8 already supplies the
correct interface. On each selected short leaf l, a sufficient
condition retains its location:

$$
X_{z_l}\subseteq H_l
\cup\!\!\bigcup_{\substack{\text{selected }27s\text{ output}\\
                         \text{parent matches }l}}[r]_s
\cup\!\!\bigcup_{\substack{\text{selected }81s\text{ output}\\
                         \text{leaf equals }l}}[r]_s.
\tag{PC28}
$$

Here H_l is the already paid base on that leaf, all phases are
literal, and every cofactor uses one permanent plan for all leaves.
Demanding all X_{z_l} is a sufficient condition; covering the exact
unpaid inverse traces there can require less. The remaining long
inverses and other deletion liabilities must retain the existing
payment from Report853. These existing interfaces, rather than a
new general selection statement, determine whether a proposed
mixed subcover can actually improve the original cover.

## The two-encloser repair applies to each deleted group of top traces

PC22 does not require enclosing all of X_z. For every actual top
original i of old word z, write its cofactor trace as

$$
T_i=X_z\cap[\rho_i]_{m_i},\qquad d_i=9qm_i.
$$

Fix two different nonunit divisors s_1,s_2 of W and two literal
phases r_1,r_2. Then global count minimality forces

$$
\#\{i:\ i\text{ is top at }z,\quad
 T_i\subseteq[r_1]_{s_1}\cap[r_2]_{s_2}\}\le3.
\tag{PC29}
$$

Otherwise delete any four such originals and retain every other
original. A point in the complete simultaneous deletion hole has
old word z, avoids all q-free originals and belongs to a deleted
original, so its cofactor lies in one of those four T_i. The same
three fresh labels 27,27s_1,27s_2 from PC22 cover every integer
lift of the hole. Four deletions and three insertions contradict
count minimality.

No connected-component condition or enclosure of the other top
traces is needed. The actual trace can be smaller than its full
cofactor coset, so PC29 also detects enclosures forced by the
retained-family residual. It is a local application of the existing
complete-hole three-child repair, not a new generic exchange.

A transient Lean consumer checks this precise locality: its
enclosure hypothesis applies only to each deleted original's class
after excluding all q-free originals. It constructs the smaller
whole odd distinct covering system using the previously checked
repair. The four checked axiom closures are standard-three only.

## Prime rank alone does not enforce a two-owner cofactor capacity

The following control reuses the sibling/path mechanism of
Pach--Tardos--Toth,
[*Indecomposable Coverings*](https://doi.org/10.4153/CMB-2009-048-x),
Canadian Mathematical Bulletin 52(3) (2009), 451--463,
Definition 2.3 and its following argument on pages 454--455.
An omitted child at every ternary node determines an entirely
omitted root-to-leaf path. The congruence realization below uses
that existing mechanism; it is not a new cover-decomposition result.

It has 110 complete colors, 27 cofactor primes, at most three
owners per numerical cofactor, a connected source-incidence graph
and cofactor hull one, yet admits no cover using at most two owners
per cofactor. Its exponent profile satisfies only the older GHA11
bound, not the stronger current CD51/CD87 profile. Its source is a
prescribed mask, not an actual retained-family residual. These
limitations are part of the control.

### Literal congruence construction

Fix the old word z=2 modulo nine. List the 25 primes from 11 through
109 as p_i. Set k_i=5 on the
first ten axes and k_i=4 on the other fifteen, and put

$$
\sum_i k_i=110,\qquad
W=5^{15}7^{10}\prod_i p_i^{k_i}.
\tag{PC30}
$$

For epsilon=0,1, let X_epsilon consist of the CRT points with
coordinates epsilon modulo both 5^15 and 7^10 and, independently,

$$
x\equiv3\epsilon+\sum_{h=1}^{k_i}j_{i,h}p_i^{h-1}
        \pmod{p_i^{k_i}},\qquad j_{i,h}\in\{0,1,2\}.
$$

The component shift affects only the first digit. For a level
1<=a<=k_i and prefix v in {0,1,2}^{a-1}, define

$$
C(v)=\sum_{h=1}^{a-1}v_h3^{h-1},\quad D=2C(v)+\epsilon,
\quad t=p_i^a5^{D\bmod16}7^{\lfloor D/16\rfloor}.
\tag{PC31}
$$

Here D<=161, so the two tag exponents are at most 15 and 10.
The dynamic prime, its exponent and the tag pair recover i,a,v
and epsilon. Thus every block has a different nonunit cofactor
t dividing W. Its three owners j=0,1,2 have the fixed CRT phases

$$
\rho\equiv3\epsilon+\sum_{h=1}^{a-1}v_hp_i^{h-1}
                           +jp_i^{a-1}\pmod{p_i^a},\qquad
\rho\equiv\epsilon\pmod{t/p_i^a}.
\tag{PC32}
$$

Give the whole block color
\(c(i,a)=2+\sum_{h<i}k_h+a\), ranging from 3 to 112.
The original label of owner j is 3^j*113*t, with this q-color,
old ternary phase 2 modulo 3^j, and cofactor phase rho. All labels
are distinct odd nonunits. Original classes of different colors
are disjoint modulo 113; within one color their dynamic prefixes
differ. Hence the original APs are pairwise disjoint and have
private integers.

On X_epsilon, the trace of an owner is exactly the set of points
with its specified first a dynamic digits and component. All tag
conditions hold automatically there; the first dynamic digit
separates the two components even when the tag is one. Therefore
each of the 110 colors partitions X_0 union X_1.

Add one bridge point b: its two tag coordinates are one, one
dynamic axis is 3 modulo its full prime-power coordinate, and
every other dynamic axis is zero. At each zero axis and every
level its prefix has C=0, epsilon=0 and tag one, so its child-zero
owner contains b. At the distinguished axis the epsilon=1,
C=0 child-zero owner has tag 5 and contains b. Each color still
has exactly one owner at b. Define

$$
X=X_0\cup X_1\cup\{b\},\qquad |X|=2\cdot3^{110}+1.
\tag{PC33}
$$

Within either component, supports on different dynamic axes
intersect by independent coordinate choices, connecting its
owner-incidence graph. The bridge belongs to owners from both
components, so the graph on X is connected. Also zero belongs
to X_0, while X_1 contains a point equal to one modulo 5 and 7
and three modulo every dynamic prime. Its difference from zero
is coprime to W. Thus the cofactor hull of X is one.

### Every block-capacity selection misses one common point

Any selection of at most two owners per cofactor omits a child
at every node. In each dynamic axis, follow those omitted children
from its root to depth k_i, fixing epsilon=0. CRT combines all
25 paths with the zero tag coordinates into one point of X_0.
At each color, its unique owner is the omitted child of the visited
node. Every other owner misses that same point. Thus the selected
union fails to cover X. The argument uses a single simultaneous
source point, not independently chosen witnesses for the blocks.

The construction has

$$
2\left(10\frac{3^5-1}{2}+15\frac{3^4-1}{2}\right)=3620
\quad\text{blocks},\qquad10860\quad\text{owners}.
$$

It shows why one omission per complete color cannot be replaced
by one omission per numerical cofactor block on the basis of
prime rank, private points, connectedness and global hull alone.
The original family is a noncover: setting every dynamic first
digit to six misses every original. No q-free bank, numerical
divisor closure or equality of X with the exact residual is
asserted.

### Existing stronger hypotheses exclude this control

The current CD87 bound has exponent at most one at every p>=29;
PC30 uses exponents four or five there. Moreover the bridge uses
child zero at every axis, so it belongs to no top trace, whose
row is j=2. In particular the epsilon-zero level-one top owners
on axes 11,13,17,19 all have traces contained in X_0 and hence in
\([0]_5\cap[0]_7\). If X were the actual X_2, these four traces
would contradict PC29 via the fresh labels 27,135,189. This second
obstruction uses only level-one owners and is independent of the
height violation. Connectedness and hull one do not evade it.

A scoped transient Lean check uses two levels on the dynamic
prime 11 and two components, with a single tag prime 5. Its eight
block moduli are 11,55,121,605,3025,15125,75625,378125. It checks
the exact congruence incidences of all 18 source points, both
complete colors, injective odd original labels, hull one and a
common missed point for every omission function. Compilation uses
default budgets, and all five axiom closures are standard-three
only. This is a check of the finite instance; the general 110-color
construction, its bridge and its failure proof above remain
ordinary mathematical deductions, not a full Lean replay.

## The current exponent budget must enter any stronger selection claim

For the actual H_3=2, q=113 branch, the existing support bound,
Report850 CD51/CD87 and the older small-prime bounds together give

$$
\begin{array}{c|cccc|c|c}
p&5&7&11&13&17,19,23&29\le p\le109\\\hline
v_p(W)\text{ upper bound}&15&13&12&11&2&1
\end{array}
$$

There are twenty primes in the last column. Therefore

$$
\Omega(W)\le77,\qquad
\tau(W)\le16\cdot14\cdot13\cdot12\cdot3^3\cdot2^{20}
          =989318873088.
\tag{PC34}
$$

Here Omega counts prime factors with multiplicity, unlike omega
in PC19. PC30 has Omega(W)=135 and does not meet PC34. The upper
bound on W itself has 300 bits and exceeds 3^110, so the elementary
random-omission criterion |X|<3^110 is not supplied by this
exponent envelope alone. Whether n>Omega(W), or the additional
actual-source restriction PC29, supplies a useful cofactor-capacity
selection remains unresolved. Even such a selection would still
need the permanent prefix service in PC28 before yielding an
original whole-cover contradiction.

## Distinct colors permit complete private regions in the repair

Keep the same actual minimal whole cover, H_3=2, q=113 and a fixed
safe old word z. For a top original i at this word, let P_i be the
projection modulo W of its complete original private region:

$$
P_i=\{x\bmod W:\ x\in[\rho_i]_{d_i},\quad
                 x\notin[\rho_j]_{d_j}\text{ for every }j\ne i\}.
\tag{PC35}
$$

These sets are nonempty by original irredundancy and satisfy
P_i subset T_i. They are not individual chosen witnesses. They
retain all private integers, including every lift in the original
period.

Suppose J consists of four top originals at z with different first
q-digits. Their original integer classes are pairwise disjoint.
Consequently the complete joint hole after deleting J is exactly
the union of their complete private regions. Indeed, a point in
that hole has a deleted owner by whole coverage, no retained owner
by definition, and no other deleted owner by q-phase disjointness.
The reverse inclusion holds directly.

Thus PC29 strengthens on this distinct-color family: it suffices
that the four P_i, rather than the larger T_i, lie in the same two
specified different nonunit cofactor cosets. The three fresh labels
27,27s_1,27s_2 then pay the complete joint deletion hole. This is an
application of the existing whole-hole repair. Without disjoint
deleted classes, a union of private regions need not equal the
simultaneous hole, so the distinct-color condition cannot be dropped
from this argument.

## Pure guards bound colors with a concentrated private projection

Let M divide W and have two different nonunit divisors. Define B_M
to be the set of top colors c at z for which some top original i
of color c has its entire nonempty P_i in one residue modulo M.
Let R_M be the residues modulo M avoiding every actual pure
prime-power original whose modulus divides M. Then

$$
|B_M|\le3|R_M|.
\tag{PC36}
$$

For a fixed r in R_M, four distinct colors with private projections
contained in [r]_M would give four originals in the preceding repair:
choose two distinct nonunit divisors of M and reduce r to their
phases. Hence each residue can account for at most three colors.
For each color in B_M, choose one qualifying original and residue;
its private points avoid every pure guard, so its residue belongs
to R_M. Counting the fibers of this one simultaneous choice proves
PC36. The count is of colors, not of all top originals.

Numerical divisor closure supplies all these pure prime-power
guards. For a fixed prime p, their classes at powers p through p^e
are pairwise disjoint: otherwise a higher-power original would be
contained in a lower-power one and have no private integer. Thus
the exact guard-avoiding count is

$$
|R_M|=\prod_{p^e\parallel M}
 \left(p^e-\sum_{j=1}^{e}p^{e-j}\right).
\tag{PC37}
$$

The product uses CRT only between distinct prime directions. No
independence of the actual P_i or X_z is assumed; other retained
originals can further restrict their residues.

In particular, when the respective divisibility conditions hold,

$$
\begin{array}{c|c|c|c}
M&|R_M|&|B_M|\text{ upper bound}
  &\text{top colors outside }B_M\text{, at least}\\\hline
25\mid W&25-5-1=19&57&48\\
35\mid W&(5-1)(7-1)=24&72&33
\end{array}
\tag{PC38}
$$

The last column uses the same at least 105 top colors at z from
PC21. For each color outside B_M, every top original of that color
at z has private points in at least two different M-residues. In
particular, none of those top cofactors is divisible by M. This
conclusion concerns complete private projections and is stronger
than merely excluding a particular top cofactor label.

The sets of 48 and 33 colors need not coincide. Different colors'
cofactor projections may overlap, so these counts cannot be added
as distinct source points or converted into a density bound. PC38
supplies no common choice across different old words, no capacity-two
selector, and no prefix allocation. It restricts where a proposed actual
obstruction can concentrate while retaining the full deletion
liability; it does not close the q=113 branch or the unrestricted
odd covering problem.

A transient Lean check verifies the distinct-color private-region
repair, its bucket bound under actual whole-cover minimality,
the nonempty-private-set guard interface, finite fiber counting,
and the exact 25/35 guard counts and numerical consequences.
The default-budget build succeeds with fifteen axiom closures
contained in the standard three. These are reuse checks; the
general prime-power product PC37 is an ordinary CRT deduction,
not a claimed additional compiled theorem.

## Modulus-sum minimality reduces the private bucket capacity to two

PC36 uses class-count minimality alone. The same actual EB1 family
also minimizes the modulus sum among all whole covers with that
class count. Suppose a private-phase bucket contains three different
top colors, and select one original from each. Write their numerical
moduli as 9q m_1,9q m_2,9q m_3. The same complete private-region
argument permits replacing precisely these three originals by
27,27s_1,27s_2. The number of classes is unchanged; freshness and
distinctness are the same as in the four-original repair.

The exact strict-cost condition is

$$
3(1+s_1+s_2)<q(m_1+m_2+m_3).
\tag{PC39}
$$

Every m_i is positive. Consequently the condition
1+s_1+s_2<q suffices uniformly, without a phase-dependent estimate
of the removed moduli. The new sum is then at most
27(1+s_1+s_2)<27q, whereas the removed sum is at least 27q.
This contradicts same-count modulus-sum minimality. Thus, whenever
M|W has two distinct nonunit divisors satisfying this sufficient
cost condition,

$$
|B_M|\le2|R_M|.
\tag{PC40}
$$

This is a direct whole-cover exchange. It does not allocate
independently optimized prefixes or ignore other deleted originals:
there are exactly three deleted originals, and their complete joint
hole is covered.

For q=113, the following choices give the resulting bounds; each
row retains its condition M|W:

$$
\begin{array}{c|c|c|c|c}
M&(s_1,s_2)&|R_M|&|B_M|\text{ upper bound}
 &\text{top colors outside }B_M\text{, at least}\\\hline
25&(5,25)&19&38&67\\
35&(5,7)&24&48&57\\
49&(7,49)&41&82&23\\
55&(5,11)&40&80&25\\
65&(5,13)&48&96&9
\end{array}
\tag{PC41}
$$

For 49 the pure 7 and 49 originals exclude seven and one disjoint
residues, leaving 41. For 55 and 65, CRT gives respectively
4 times 10 and 4 times 12 guard-avoiding residues. Each displayed
1+s_1+s_2 is less than 113.

There is now a simultaneous consequence on one fixed old word.
If both 25 and 35 divide W, the same set C_z of at least 105 top
colors satisfies

$$
|C_z\setminus(B_{25}\cup B_{35})|
 \ge105-38-48=19.
\tag{PC42}
$$

For every one of these colors, every top original at z has its
complete private projection varying modulo both 25 and 35.
This is counting the union of two bad-color sets, not combining
separately chosen source points. Two private residues can already
give both variations; neither three private residues nor positive
source density follows. A capacity-two cofactor selector and the
permanent prefix service of PC28 still remain to be established.

In fact each such top original has one pair of its own complete
private points separating both readouts:

$$
\exists x,y\in P_i:\quad
x\not\equiv y\pmod{25},\qquad
x\not\equiv y\pmod{35}.
\tag{PC43}
$$

To see this, take a pair separating the first readout. If it also
separates the second, it suffices. Otherwise both points have the
same second readout. A third point with a different second readout
must differ in the first readout from at least one of the original
pair. That pair separates both. The argument uses only points in
the same P_i; it supplies no single pair shared by different
originals or colors.

Two scoped transient Lean checks verify the same-count whole-hole
replacement with its exact sum comparison, the three-color
private-region consumer and capacity-two bucket bound, the five
guard-count interfaces, the simultaneous 19-color count and the
same-private-pair implication. Both builds exit successfully under
default budgets; all 29 reported axiom closures use only the
standard three. No new retained Lean declaration is introduced
for these reuse applications. The original branch assumptions,
the at least 105 top colors and the existence of the pure guards
remain the explicitly cited inputs to these consumers.

## A single actual top label bounds its entire divisor inventory

Keep the same EB1 whole cover and the PC34 exponent envelope.
Suppose 9qm is an actual original label, q=113, m|W. For each
composite d|m, define the exact actual-guard residual

$$
R_d=\{r\bmod9d:\ r\not\equiv a_e\pmod e
       \text{ for every original label }e\mid9d\}.
\tag{PC44}
$$

This residual is auxiliary; it does not replace the source X_z.
The subscript here specifies a cofactor d and the ambient modulus
9d, unlike the pure-guard residual R_M in PC37.

Report385 DR8 already bounds by two the number of proper original
multiples of 9d in any one phase modulo 9d. Its hypotheses hold:
the ternary height is full, 3 is the smallest support prime, and
the composite d has at least three divisors. This is an existing
whole-AP repair, not a consequence of independent private witnesses.
Choosing a proper nonunit divisor p of d gives fresh labels
27,27p,27d covering that entire phase. Every proper original multiple
of 9d is greater than 27d, because its odd quotient exceeds one and
is coprime to 3. Three such originals could therefore be replaced
at the same count with a strictly smaller modulus sum.

Divisor closure of the single actual label 9qm supplies exactly
2 tau(m/d) original top labels 9dt, where t divides qm/d. Here
q does not divide m, so the factor two is the coprime divisor-count
formula. Remove the one label 9d from this inventory. Every remaining
class is disjoint from every actual guard e|9d: comparable originals
cannot intersect in an irredundant family. Its reduced phase thus
belongs to the same R_d in PC44. The existing capacity-two bound gives

$$
2\tau(m/d)-1\le2|R_d|,
\qquad \tau(m/d)\le|R_d|.
\tag{PC45}
$$

The second inequality uses integrality. Excluding 9d is essential:
its phase does not avoid its own guard. This refines the actual-label
ancestor count of Report385 CPA5 by retaining all actual divisor
guards. Neither W nor 9qW is assumed to be an original modulus.

The actual 3 and 9 originals leave five residues modulo nine.
For a prime p with p^2|m, the actual p and p^2 originals remove p and one disjoint
residues modulo p^2. CRT between these two prime axes yields

$$
\tau(m/d)\le5d\quad(d\mid m\text{ composite}),\qquad
\tau(m/p^2)\le5(p^2-p-1)\quad(p\text{ prime},\ p^2\mid m).
\tag{PC46}
$$

Additional mixed guards can only decrease the exact residual.
No phases are optimized independently in this deduction.

## Each actual top cofactor has at most 25 prime factors with multiplicity

Under PC34 and PC46,

$$
\Omega(m)\le25\qquad\text{for every actual original }9qm.
\tag{PC47}
$$

Suppose instead Omega(m)>=26. In the squarefree case, m contains
at least 26 of the 27 available primes. Two of 5,7,11 divide m;
their product d is at most 77. Then
tau(m/d)>=2^24>385>=5d, contradicting PC46.

Otherwise let p be the smallest squared prime. It belongs to
5,7,11,13,17,19,23. In m/p^2, smaller primes have exponent at most
one, the p cap is lowered by two, and all other caps are those of
PC34. The remaining exponent sum is at least 24. Decreasing
coordinates until their sum is exactly 24 cannot increase the
divisor product. The following exact minima therefore suffice:

$$
\begin{array}{c|r|r}
p&\min_{\sum e_i=24}\prod_i(e_i+1)&5(p^2-p-1)\\\hline
5&168&95\\
7&312&205\\
11&792&545\\
13&138240&775\\
17&9437184&1355\\
19&12582912&1705\\
23&16777216&2525
\end{array}
\tag{PC48}
$$

Each row contradicts PC46. The finite optimization uses the exact
recurrence D_0(0)=1, D_0(t)=infinity for t>0, and

$$
D_{j+1}(t)=\min_{0\le a\le\min(c_j,t)}
                 (a+1)D_j(t-a),\qquad0\le t\le24.
\tag{PC49}
$$

Here c_j is the residual cap just described. Induction on j proves
that D_j(t) is the minimum product for those first j coordinates:
each exponent vector has a unique last coordinate a, and conversely
every finite entry and choice a gives a feasible extended vector.
The [exponent-budget program](../../../frontier/cover-geometry/cd-prime-capacity-controls/top_cofactor_exponent_budget.py)
checks every recurrence entry, an attaining vector for each row,
and the 28 possible squarefree supports. Its
[exact data](../../../frontier/cover-geometry/cd-prime-capacity-controls/top_cofactor_exponent_budget.json)
retain all caps and integer tables. No floating-point comparison
or sampled phase assignment is used.

A three-owner numerical block in the H_3=2, G=1 moving family has
the actual labels qm,3qm,9qm, so PC47 applies to every such block.
It does not give Omega(W)<=25: different actual cofactors may have
a larger least common multiple. It also supplies neither a
capacity-two selector nor the complete prefix payment in PC28.

The exponent vector m=7^13*11^12 has Omega(m)=25 and satisfies
all 179 composite-divisor inequalities tau(m/d)<=5d and both
square-guard inequalities in PC46. In particular the latter read
156<=205 and 154<=545. It is a witness in the exponent relaxation,
not an actual phase assignment, exact guard residual or whole cover.
Thus PC34 and PC46 alone cannot lower 25 to 24.

A scoped transient Lean check verifies the proper-multiple phase
capacity, same-count whole-hole replacement, actual indexed-ancestor
count, coprime divisor doubling, actual-phase guard reduction and
the finite inventory consumer in PC45. Its default-budget build
exits successfully, with fourteen axiom closures contained in the
standard three. Actual divisor closure, comparable-class disjointness
and the guard counts are explicit inputs or ordinary source bridges;
this is not an end-to-end formalization of PC44--PC49 or Erdős #7.

The seven product lower bounds in PC48 also have a scoped Lean
check quantified over every vector of 27 natural exponents under
the stated caps and with total at least 24. It checks 189 finite
transition inequalities, then composes the 27 prefix inequalities
for an arbitrary vector. The sum coordinate saturates at 24, so
the proof covers totals greater than 24 directly. All seven axiom
closures are standard-three only; compilation uses default budgets.
This verifies universal product bounds, rather than just the seven
displayed numerical comparisons. The original-cover-to-exponent
and actual-guard bridges remain as specified above.

## Different actual top labels share the same divisor capacity

Let M_top be the set of all m for which 9qm is an actual original.
It is closed under taking divisors. For a composite d with
M_d={m in M_top:d|m} nonempty, d itself belongs to M_top.
Every t in M_d supplies both actual labels 9t and 9qt. These two
inventories are disjoint because all t are prime to q. Their union
has 2|M_d| members. Excluding 9d once puts every remaining literal
phase into the same actual R_d. Thus the PC45 counting argument gives

$$
|M_d|\le |R_d|.
\tag{PC50}
$$

This is a joint stock constraint, rather than a separate allowance
for every maximal original. In particular, for any finite list of
actual top cofactors m_j sharing d,

$$
\left|\bigcup_j\{t:d\mid t,\ t\mid m_j\}\right|\le |R_d|.
\tag{PC51}
$$

The union is contained in M_d. For two such cofactors, its exact
cardinality is

$$
\tau(m_1/d)+\tau(m_2/d)
 -\tau(\gcd(m_1,m_2)/d)\le |R_d|.
\tag{PC52}
$$

Indeed, division by d identifies each set with the divisors of
m_j/d, and their intersection with the divisors of
gcd(m_1/d,m_2/d)=gcd(m_1,m_2)/d. All these labels are supplied by
actual originals; no label at the least common multiple is asserted.

For example, the two exponent vectors
m_1=7^13*11^12 and m_2=7^13*13^11 separately satisfy PC34 and PC46.
The program checks all 179 and 165 relevant composite divisors,
respectively, together with their square-guard bounds. But they
cannot both be actual top cofactors in this family. At d=49,

$$
\tau(m_1/49)+\tau(m_2/49)-\tau(\gcd(m_1,m_2)/49)
 =156+144-12=288>205\ge |R_{49}|.
\tag{PC53}
$$

Separate feasibility here means only feasibility in the exponent
relaxation. Neither vector has been supplied with actual phases.
The conclusion is that their simultaneous occurrence is excluded
even at this necessary counting level.

A further scoped transient Lean check verifies the disjoint doubled
inventory with its excluded base, finite fiber bound, divisor-set
intersection and union, the exact 288 count, the contradiction with
205, and the second vector's individual checks. The default-budget
build exits successfully and all nine axiom closures are contained
in the standard three. The supplier of these inventories is the same
explicit actual-source bridge used in PC45; this does not turn a
numerical relaxation into a phase construction or settle the selector.

## Coarse joint stock ceilings still allow many shallow cofactors

PC21 gives at least 105 top originals on each of the five safe old
words, hence at least 525 distinct actual top cofactors. The five
sets are disjoint by old word, and distinct labels 9qm give distinct m. The
relaxed numerical consequences of PC50 do not contradict this count.
Let S be the 27 cofactor primes from 5 through 109 and set

$$
\mathcal M=\left\{\prod_{p\in A}p:A\subseteq S,\ |A|\le3\right\}.
\tag{PC54}
$$

This is a divisor downset with
|M|=1+27+351+2925=3304. Every member is squarefree and has Omega
at most three; the lcm has Omega 27. For d in M with two prime
factors, exactly 26 members are divisible by d: d itself and its
25 extensions by one further prime. For a three-prime d there is
only d itself. Thus every composite d in this downset satisfies

$$
|\mathcal M_d|\le5\prod_{p\mid d}(p-1)\le5d.
\tag{PC55}
$$

The first right side is at least 120 for pairs and 1200 for triples,
whereas the left sides are 26 and one. Square-divisor tests are
vacuous. Any union of principal inventories is contained in the
corresponding M_d, so these same numerical ceilings also hold for
all such unions simultaneously.

The experiment above checks integer divisibility for all 3276
composite fibers. A scoped transient Lean application of Mathlib's
fixed-subset counts and prime-product identities verifies the
3304 count, divisor-downset interface and fiber counts for any
27-element prime pool. Its default-budget build succeeds and all
eight axiom closures are standard-three only.

This control refutes only an inference from the displayed relaxed
numerical ceilings to |M|<525. It supplies no original phases, exact
R_d, complete color covers, selector or paid replacement. In
particular it does not satisfy or refute PC50 with its actual-source
residual. Further progress must retain more of that joint source
than its coarse stock ceilings.

## A prime bipartition repairs the entire deleted union

Continue under the global count-then-modulus-sum minimality of EB1,
with H_3=2 and q=113. Fix an old word z modulo nine and one cofactor
phase vector w. Let P be the actual cofactor-prime pool and r=|P|.
For each actual q-bearing top original i at z, put

$$
A_i(w)=\{p\in P:p\mid m_i,\ \rho_i\equiv w\pmod p\}.
\tag{PC56}
$$

These are first-prime phase tests; membership does not assert that
the whole original contains w. In particular an original may match
several coordinates while missing another coordinate or a deeper
prime digit.

Split P into disjoint sides L and R. Select any K actual top
originals whose A_i(w) meet both sides, and choose a pair
p_i in A_i(w) intersect L, t_i in A_i(w) intersect R for each.
Let L' and R' be the sets of used primes and V=|L'|+|R'|.
The following fresh classes cover the entire union of these K
original APs:

$$
\begin{array}{c|c|c}
\text{ternary phase modulo }27&\text{cofactor condition}&\text{label}\\\hline
z&\text{none}&27\\
z+9&x\equiv w\pmod p,\ p\in L'&27p\\
z+18&x\equiv w\pmod p,\ p\in R'&27p.
\end{array}
\tag{PC57}
$$

CRT defines each displayed class because all tags are prime to
three. Every integer in any deleted original has old word z and
satisfies both selected prime congruences. Its next ternary digit
therefore places it in the pure row, its selected left row, or its
selected right row. This proves coverage at every integer lift,
without requiring a common q-color or identifying the deletion
hole with a union of separately chosen private witnesses. The
complete simultaneous hole is contained in the deleted union.

There are 1+V new labels. They are distinct because the sides are
disjoint and all tags exceed one, and fresh because every original
has ternary height at most two. Let M=sum_i m_i. Distinct selected
primes divide each m_i, so p_i t_i divides m_i. Since both primes
are at least five,

$$
\sum_{p\in L'\cup R'}p
\le\sum_i(p_i+t_i)
\le\sum_i p_i t_i
\le M,
\qquad
27(1+M)<9\cdot113M\quad(M\ge1).
\tag{PC58}
$$

If K>V, the repair has at most K classes and costs strictly less
than the deleted classes. Strictly fewer classes contradict count
minimality; equal count contradicts the secondary minimum. Hence
every such selection satisfies K<=V. In particular,

$$
\#\{i:A_i(w)\cap L\ne\varnothing,
          \ A_i(w)\cap R\ne\varnothing\}\le r.
\tag{PC59}
$$

The empty-side cuts have zero owners. The comparison class in EB1
allows higher ternary heights; restricting the minimum to H_3=2
covers would not justify this exchange.

## Averaging all cuts gives a pointwise support budget

For a fixed nonempty matching set A of cardinality a, exactly
2^r-2^(r-a+1) of the 2^r subsets L split A between L and its
complement. The two excluded kinds put all of A on one side or
the other; they are disjoint because A is nonempty. An empty A
is split by no cut. Define f(0)=f(1)=0 and f(a)=1-2^(1-a) for
a>=2. Summing PC59 over all cuts and using the two empty-side
cuts gives, for r>=1,

$$
\sum_i f(|A_i(w)|)
\le r(1-2^{1-r})<r.
\tag{PC60}
$$

This is a finite double count, not an independence assumption on
the original phases. The averaging is over auxiliary cuts of one
fixed prime pool and keeps all original phases and the same w.
When r<=27, the resulting upper bounds for owners whose matching
sets have at least the indicated size are

$$
\begin{array}{c|rrrrr}
\text{matching primes at least}&2&3&4&5&6\\\hline
\text{number of q-bearing top owners at most}&53&35&30&28&27.
\end{array}
\tag{PC61}
$$

At an actual point w contained in an original, its matching set
is its entire distinct-prime support. Thus PC61 also bounds the
incident top owners of each support size. Unlike Report861 CP18,
this count includes only q-bearing tops: PC58 uses their q price
factor. The two estimates have different scopes and neither
licenses dropping retained q-free originals from CP18.

## Every actual point needs service from lower rows

In the height-one branch of PC34, restrict to the at least 110
complete colors outside the unit-cofactor labels q,3q,9q. Every
moving cofactor is then nonunit. At a fixed actual point (z,w),
the incident top originals with cofactor p^k are bounded as follows.
For each p there is at most one k=1 owner, since its numerical
label is 9qp. All owners with k>=2 are proper descendants of the
same actual composite parent 9p^2. Their phases agree modulo
9p^2 at this one point, so DR8 bounds their number by two.
The exponent caps further restrict axes of height two or one.
Consequently,

$$
\begin{array}{c|c|c}
\text{prime axes}&\text{owners per axis at most}&\text{total at most}\\\hline
5,7,11,13&3&12\\
17,19,23&2&6\\
29,31,\ldots,109&1&20
\end{array}
\qquad N_{\rm prime\ power}\le38.
\tag{PC62}
$$

If an axis or its square is absent, its relevant contribution is
zero. Divisor closure supplies 9p^2 only when such a descendant
exists; no least-common-multiple label is substituted for an
actual original. Matching only modulo p would not suffice for
the DR8 step: the owners counted here contain the actual w and
therefore agree at p^2 as well.

PC61 and PC62 give at most 53+38=91 incident moving top owners,
hence at most 91 colors with an active top owner. Every one of
the 110 complete color families covers the same actual X_z.
Thus at every point of X_z,

$$
\#\{c:\text{some lower-row original of color }c
                  \text{ is active at }(z,w)\}\ge19.
\tag{PC63}
$$

This is a pointwise lower-row multiplicity on the original common
source. The nineteen colors may depend on w. It does not give
nineteen fixed complete lower-row color covers or positive density
for one row. A fixed union of lower owners is nevertheless available,
as the following selector construction shows. Permanent prefix
payment and an odd-cover contradiction do not follow from PC63.

## Hereditary cut capacity sharpens the mixed-top bound

For every top owner with at least two matching primes at w, choose
two of them. Regard the owner as one edge joining these primes,
retaining parallel edges for different original owners. There are
no loops. For any vertex subset S and any cut of S, the selected
crossing edges form a packet to which PC57--PC58 applies, with all
used tags inside S. Hence its edge count is at most |S|.

Here is a general finite graph consequence of exactly that
hereditary cut condition. Every nonempty induced vertex set S has
strictly fewer than 2|S| edges: each edge crosses half the cuts,
whereas the empty cut has zero edges and every cut has at most
|S|. The degree sum is twice the edge count, including parallel
edges, so S has a vertex of degree at most three. Delete such a
vertex, color the remaining vertices with four colors inductively,
and restore the vertex using a color not present on its at most
three neighbors. This constructs a proper four-coloring.

Take the three balanced partitions of the four color classes into
two pairs. Every edge crosses exactly two of these cuts. Each
cut has at most r edges, and therefore

$$
2N_{\rm mixed}\le3r,
\qquad N_{\rm mixed}\le40\quad(r\le27).
\tag{PC64}
$$

The argument uses the cut bound on every induced vertex set, not
just on the original full pool. It handles parallel edges directly
and does not assume a coloring or a bound on maximum degree.
It reuses finite double counting and the elementary greedy-coloring
construction; no extremal-graph novelty is claimed.

Combining PC64 with PC62 improves the pointwise conclusion to

$$
N_{\rm top}\le78,
\qquad N_{\rm lower\ colors}\ge32.
\tag{PC65}
$$

## A fixed two-owner cofactor selector on the entire actual source

Let E_0 be the complete q-free residual on the full 9W carrier,
as in PC25. Take the fixed set of all moving originals of colors
in U whose ternary row is zero or one, and strip their q-factor
while preserving their literal old ternary and cofactor phases.
At every point of E_0, PC63 already supplies a member of this
set; PC65 supplies at least 32 distinct serving colors. This
holds on every safe old word, not just on a selected private point.
Thus the same fixed union covers all of E_0.

For any numerical cofactor m the selected originals can have only
the labels qm and 3qm. Distinct original moduli imply

$$
E_0\subseteq\bigcup_{i\in S_{<2}}\widetilde R_i,
\qquad
\#\{i\in S_{<2}:m_i=m\}\le2.
\tag{PC66}
$$

There is no need to choose the same 32 serving colors at every
point: the owner set S_<2 itself is fixed before evaluating any
point. Even the weaker PC63 bound suffices for PC66.

One can also require every selected color to be individually
incomplete. Fix one safe word z_* and let C_* be precisely the
colors in U having a top original at z_*. PC21 excludes at most
five colors from C_*. Restrict the fixed lower-owner selection
to these colors. At every point of E_0 at least

$$
32-5=27
\tag{PC67}
$$

serving colors remain; using PC63 instead gives 19-5=14, also
enough. For each c in C_*, an actual top original at z_* has a
global private integer. Its projection belongs to E_0 and is
missed by all lower originals of c: since G=1, a same-color
stripped lower owner at that projection would also cover the
original private integer. Consequently this one fixed selection
simultaneously has

$$
E_0\subseteq\bigcup_{c\in C_*}\bigcup\mathcal L_c,
\qquad E_0\nsubseteq\bigcup\mathcal L_c\ (c\in C_*),
\qquad\#\{i\in\bigcup_c\mathcal L_c:m_i=m\}\le2.
\tag{PC68}
$$

Here each L_c consists of the actual stripped lower owners of c;
no phase is selected independently of its original. The all-lower
choice also respects any fixed actual masked component: an owner
active on that component intersects it and belongs to the same
component. This assertion concerns stripped-source coverage, not
preservation of each original q-color's service separately.

PC66--PC68 close the projected two-owner selection gap in the
stated H_3=2, G=1, q=113 branch using the actual source, exponent
caps and extremal exchanges. They do not follow from prime rank
alone, and do not contradict the prescribed-mask control PC30--PC33.
The remaining obligation is PC28: assign permanent fresh prefixes
with distinct numerical labels while covering the complete joint
deletion hole, including any additionally deleted parents. Keeping
all lower owners in a projected cover does not yet supply that
assignment or its count and modulus-sum payment.


The graph bound PC64 is formalized in
`D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity.lean` with a
constructed four-coloring; its finite applications include a complete
four-vertex graph, a parallel-edge equality case, and the r<=27
bound. Scoped Lean checks also cover the whole-integer bipartition
repair, its fresh-label and strict-cost conditions, the pure-power
finite-fiber count 38, and the fixed lower-selector and excluded-color
counting steps. These checks use only the standard three axioms.
The suppliers from the original minimal cover to the exponent caps,
common residual, and private-point hypotheses remain the explicit
arithmetic deductions above; this is not one end-to-end formal proof
of those suppliers or of Erdős #7. Permanent prefix assignment and
complete deletion payment remain unproved.
