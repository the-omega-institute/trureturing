[Index](../../../marked_head_profile.md) · [Complete component source](861-complementary-phase-repair-and-pair-anchor-rigidity.md#exact-deletion-hole-of-a-masked-component) · [Existing ternary transport](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#143-actual-joint-hole-sources-sharpen-the-low-row-inventory-and-first-q-prefix-repair) · [Component code](850-cofactor-dependent-protected-codes.md#one-component-contains-a-rectangular-top-inventory)

# Three complete top-row colors admit one fresh whole-component exchange

In the actual common-source component of Report861, at most two
colors can have all their original classes in the top ternary row.
Three such complete color covers can be assigned to the three next
ternary digits. They replace the entire component using distinct
fresh odd moduli and strictly fewer classes when more than three
colors are available.

Consequently, for n moving colors, at least n−2 colors must contain
an original in a lower ternary row. Combining this with the existing
same-component five-word requirement gives at least
$6n-27$ component originals, hence 471 at n=83. This is a necessary
condition for the specified branch of a globally minimal whole
cover. It does not prove that the branch or an unrestricted odd
cover is impossible.

## Keep the complete common source

Let the original family be one finite distinct odd nonunit whole
cover, globally minimal in class count among all such covers.
Its period has the form

$$
Q=9q^G W,\qquad q=113,\qquad (W,3q)=1.
\tag{TC1}
$$

The separate support and height envelope supplies the full moving
digit complement U with $n=|U|\ge83$. Retain the exact q-free
complement $E_0$ on the full $9W$ base. Form components from the
actual masked intersections $F_i=R_i\cap E_0$, and fix one nonempty
component C. Write $M=|C|$ and $V_C=\bigcup_{i\in C}F_i$.
Original private points ensure $V_C$ is nonempty.

The already verified common-source identity supplies both facts
needed below. Deleting precisely C leaves

$$
E_C=V_C\times
\{\text{all complete q-words whose first digit belongs to }U\}.
\tag{TC2}
$$

For every c in U, the original color family $C_c$ covers the same
entire $V_C$ and every full q-suffix at that first digit. In
particular every $C_c$ is nonempty. This is not an assertion about
separately chosen private points or a proper subset of $V_C$.

Call c a top-only color when every original in $C_c$ has ternary
row $a_i=2$. Assume for contradiction that distinct colors
$c_0,c_1,c_2$ are top-only, and let

$$
T=C_{c_0}\cup C_{c_1}\cup C_{c_2}.
\tag{TC3}
$$

Every selected original has label $d_i=9q^{j_i}m_i$ with
$j_i\ge1$. Its literal residue is $\rho_i$, and its selected color
index is $t\in\{0,1,2\}$.

## One AP per selected original

Replace this original by the single CRT class

$$
\begin{aligned}
\widehat d_i&=27q^{j_i-1}m_i,\\
x&\equiv (\rho_i\bmod9)+9t\pmod{27},\\
x&\equiv\rho_i\pmod{m_i},\\
x&\equiv(\rho_i-c_t)/q\pmod{q^{j_i-1}}.
\end{aligned}
\tag{TC4}
$$

The final quotient is integral and its congruence is vacuous when
$j_i=1$. The factors $27,m_i,q^{j_i-1}$ are pairwise coprime,
so TC4 defines one full arithmetic progression. Only the q-tail is
shifted; the original cofactor phase and old word modulo nine are
preserved. No uniform original q-height is assumed.

For any integer x in the complete deletion hole, take its next
ternary digit

$$
t=\left\lfloor\frac{x\bmod27}{9}\right\rfloor.
\tag{TC5}
$$

Keep its entire $9W$ base and choose a source q-coordinate with
first digit $c_t$ and remaining coordinate
$x\bmod q^{G-1}$. The complete color service gives a selected
original i of that color covering this source. Literal first-digit
stripping therefore supplies its original cofactor phase, its old
word modulo nine and its stripped q-tail at x. The definition of t
adds precisely the remaining ternary condition in TC4. Thus x
belongs to that one replacement AP.

Every point of the entire component hole is covered. All originals
outside C remain unchanged; points they already cover require no
new allocation. This establishes whole integer coverage after
removing C and inserting the TC4 family, including negative integer
lifts and all later q-digits. A finite common period for old and new
classes is $3Q=27q^GW$; the original period Q alone need not suffice
for the new ternary height.

## Freshness and the strict count are simultaneous

The replacement has ternary height exactly three. Every old modulus
has ternary height at most two, so no new numerical label is already
occupied outside C. New labels cannot collide with each other either:

$$
q\widehat d_i=3d_i.
\tag{TC6}
$$

The original labels are injective, and multiplication by positive
integers cancels. All new labels are odd and greater than one.
This checks numerical moduli, not merely whether two APs have
different residues. Raising the ternary height is allowed because
the original minimum is taken over all distinct odd covers, not just
those having height two.

Since n exceeds three and every color is nonempty, T is a proper
subset of C. The new family has exactly

$$
N'=N-M+|T|<N.
\tag{TC7}
$$

This contradicts global count minimality. Modulus-sum estimates and
parent-repair packets are unnecessary for this exchange.

The construction reuses the source-preserving fixed-prefix and
freshness mechanism of Report385 OHL6--OHL7. The additional input
is TC2's three already given complete color covers of the same
masked source, allowing the entire component to be removed at
arbitrary original q-heights. It does not assume that a raw inverse
of a general mixed-row class is one AP.

## A required lower-row inventory on the same component

Let $C_{<2}$ and $C_2$ be the originals in C with ternary rows below
two and equal to two. At most two colors are top-only. Every other
color has at least one member of $C_{<2}$, and different colors
have different original owners. Hence

$$
|C_{<2}|\ge n-2.
\tag{TC8}
$$

Use the exact-hole version of the existing component code CD21.
It selects a component for which at least n−5 colors occupy all five
eligible top-word cells. Each such cell
has its own original top-row label. On that same selected component,

$$
|C_2|\ge5(n-5),\qquad
M=|C_2|+|C_{<2}|\ge6n-27\ge471.
\tag{TC9}
$$

Among those top-rich colors, at least n−7 also have a lower-row
original. TC8 is stronger than counting only this intersection: it
also counts lower-row owners in colors outside the top-rich set.
The two row inventories in TC9 are disjoint and belong to the same
actual component. Their witnesses need not share a cofactor point.
No inventory on a full-support component is transferred to a smaller
masked component without proof.

This supplies a necessary coupling between the top profile and
lower-row service. It does not bound the lower-row contribution from
above, allocate shared divisor tags, or settle the simultaneous
whole-liability repair needed in the remaining mixed-row case.

## A uniform budget after choosing any one color

On the same CD21 component, remove any one color c from the
inventory. At least n−6 top-rich colors remain, each with five
top-row originals. At least n−3 colors with lower-row service remain,
each with a lower-row original. These are disjoint row inventories,
so, writing $k_c=|C_c|$,

$$
M-k_c\ge5(n-6)+(n-3)=6n-33\ge465.
\tag{TC10}
$$

This holds for every c on this same component. It uses CD21's
per-color rectangular inventory, not merely the scalar lower bound
on $|C_2|$: one color could contain arbitrarily many of the top
originals counted in that scalar bound.

For a separately certified exchange that removes C and s further
originals, inserts its $k_c$ normalized classes, and pays all
remaining liability with $23L+2$ fresh classes, the resulting count is

$$
N-M-s+k_c+23L+2<N\qquad(L\le20).
\tag{TC11}
$$

Indeed $23\cdot20+2=462<465\le M-k_c$. TC11 only evaluates
the budget of an actual legal whole-cover exchange; it does not
provide the required twenty repair groups or their simultaneous
fresh labels and phase compatibility.

## Verification scope

A scoped transient Lean check verifies the actual integer CRT
replacement, its distinct odd nonunit labels, freshness against
every original, complete integer coverage, and the strict count
comparison against global minimality. It includes arbitrary original
q-heights and all integer lifts. Global private points supply the
nonempty masked component base used by the exchange.

The same check derives the lower-row inventory, the 471 bound and
the uniform 465 bound from this exchange. CD21's top inventory is
an explicit reused premise on the same exact-hole component: the
471 application takes its scalar top-row bound, while the 465
application takes the richer per-color five-owner statement.
The check does not reprove CD21 or establish the existence of the
hypothetical minimal cover.

A separate scalar check verifies TC11 with the stated repair count,
$L\le20$, $465\le M-k_c$ and $M+s\le N$. It proves the
strict count inequality, without supplying a repair family.

The checked axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`, or are empty. The application
reuses existing source and exchange interfaces with Mathlib CRT
and finite-cardinality facts; it adds no retained binding declaration,
freeze, or new proof of unrestricted Erdős #7.
