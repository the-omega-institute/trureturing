[Index](../../../marked_head_profile.md) · [Complete color source](861-complementary-phase-repair-and-pair-anchor-rigidity.md) · [Component exchanges](866-whole-color-top-layer-exchange-forces-lower-row-service.md) · [Column carries](867-literal-column-carries-and-phase-hull-repair.md)

# Retained q-free originals and pure guards constrain height-one colors

Work with one globally count-then-modulus-sum minimal distinct odd
whole cover, including its original numerical divisor closure, in the
branch $Q=9q^GW$, $q=113$, $(W,3q)=1$. Keep the full moving-digit
set $U$: its complement consists of the first q-digits of all actual
unit-cofactor originals. Write $n=|U|\ge83$.

The complete-source hypothesis is global: for every $c\in U$, the
literal q-strips of all originals of color c cover the entire q-free
residual and every remaining q-coordinate. The conclusion below uses
this whole source, without choosing one masked component or imposing
a common cofactor witness.

The comparisons in this note need only global class-count minimality
once the stated original labels are supplied. The stronger EB1
assumption also minimizes the modulus sum. Under that stronger
assumption, the existing SC468 exchange already gives stronger row
inventories; its different verification boundary is stated below.

## Only height-one originals can collide with retained q-free labels

Let $\mathcal F$ be all original q-free classes, let $\mathcal A_q$
be all q-bearing originals, and put $K_q=|\mathcal A_q|$. For each
$c\in U$, let $C_c$ be its complete color family and $S_c$ its
literal first-digit strips. The complete-source identity gives

$$
\mathcal F\cup S_c\text{ covers every integer}.
\tag{WR1}
$$

Indeed $\mathcal F$ covers its entire complement of the residual,
and $S_c$ covers every point of the residual. To see the latter for
an arbitrary output integer x, preserve its full $9W$ coordinate
and use source q-coordinate $c+q(x\bmod q^{G-1})$ modulo $q^G$.
The source misses all q-free originals, and its first digit c
excludes every original of another color. Its actual owner therefore
strips to a class covering x. This argument includes output first
digits outside U. No protected first-digit cylinder is asserted to
be covered by a unit original.

The map from old to stripped numerical labels is $d\mapsto d/q$,
which is injective. A collision with $\mathcal F$ therefore requires
an old q-height-one original. If color c had none, WR1 would already
be a distinct odd nonunit whole cover with fewer classes: divisor
closure supplies the original numerical label q, whose first digit
is outside U, so it is deleted but never selected. Consequently

$$
\{i\in C_c:v_q(d_i)=1\}\ne\varnothing
\qquad(c\in U).
\tag{WR2}
$$

The actual q-free parents of these height-one originals exist by
whole-family numerical divisor closure. They are the only numerical
parent liabilities if all q-bearing originals are deleted at once.
This is a different exchange from retaining and carrying some of
those q-bearing originals.

## One common reflection preserves numerical distinctness

The construction works for any odd prime $p\ne q$. Let $H=v_p(Q)$
and define, using WR2,

$$
b_c=\min\{v_p(d_i):i\in C_c,\ v_q(d_i)=1\}.
\tag{WR3}
$$

Number p-digits from zero. Give a selected color c one selector
which fixes the digit positions $b_c,\ldots,2H-b_c$. Its size among
all $p^{2H+1}$ words is $p^{2b_c}$.

Write a selected original as $d_i=p^{a_i}q^{j_i}r_i$, with
$(r_i,pq)=1$. Preserve its actual other-prime phase and its literal
stripped q-tail. There are two cases.

If $j_i\ge2$, keep the literal strip unchanged. Its output label
still contains q.

If $j_i=1$, WR3 gives $a_i\ge b_c$. Use the new p-height

$$
e_i=2H+1-a_i,
\qquad
\widehat d_i=p^{2H+1-a_i}q^{j_i-1}r_i.
\tag{WR4}
$$

Preserve the original low $a_i$ p-digits and take digits
$a_i,\ldots,2H-a_i$ from the assigned selector. CRT gives one
actual AP with label WR4. This definition also works when the
selector conflicts with the original digits on their overlap:
the corresponding inverse slice is then empty, and the extra
coverage of the emitted AP is harmless.

The entire intersection of the literal strip with the assigned
selector is contained in this one output AP. The required digit
positions form a full initial segment $0,\ldots,e_i-1$; extra
selector positions can be forgotten. This containment is sufficient
for coverage and does not claim equality of the whole strip with
its enclosure.

Every altered output has p-height at least $H+1$ and is q-free.
Every unaltered output has p-height at most H and still contains q.
Thus altered outputs are fresh against all original labels, and
unaltered outputs are fresh against all retained q-free labels.

Within each output range, the p-height recovers the original $a_i$;
the q-height recovers $j_i$, and the remaining factor recovers $r_i$.
The two ranges are disjoint. Hence equality between any two emitted
labels, including emissions from different colors or different cases,
forces equality of the old numerical labels. All emissions have
distinct odd moduli greater than one.

## A finite prefix allocation supplies complete selectors

Order the digit positions as

$$
H,\ H-1,\ H+1,\ H-2,\ H+2,\ldots,0,2H.
\tag{WR5}
$$

For each b, the interval $[b,2H-b]$ is a prefix of this order.
Therefore its selectors are the cells of a nested partition, with
cell sizes $p^{2b}$.

If the available color weights sum to at least $p^{2H+1}$, process
colors in decreasing b and assign disjoint available cells of their
sizes. At each size the remaining cells are whole cells, because
every preceding size is an integer multiple of it. Stop as soon as
they fill the entire word space. If a level does not finish, use its
available colors and subdivide the remaining cells. At the last level
cells have size one, and the weight assumption guarantees completion.
Each selected color receives just one cell.

Retain every original in $\mathcal F$ and delete every original in
$\mathcal A_q$. An integer outside the q-free residual is already
covered by $\mathcal F$. For an integer in the residual, its word
chooses a selected color; the complete stripped family of that color
covers it, and the corresponding retained strip or enclosure covers
it as well. This proves coverage of all integers.

There is at most one emitted AP per selected original. The original
q is deleted and belongs to no selected moving color, so the number
emitted is strictly smaller than $K_q$, even if every moving color
was selected. Global count-minimality therefore implies

$$
\sum_{c\in U}p^{2b_c}\le p^{2H+1}-1.
\tag{WR6}
$$

The comparison cover may have larger p-height. Global minimality
allows that comparison; no fixed original period is imposed on it.

## The actual ternary height-one inventory

For $p=3$ and $H=2$, let $N_a$ count colors whose lowest ternary
row among their q-height-one originals is a. Then

$$
N_0+N_1+N_2=n,
\qquad
N_0+9N_1+81N_2\le242.
\tag{WR7}
$$

The three selector sizes are 1, 9 and 81 within the 243 five-digit
words. They respectively fix all five digits; digits 1, 2, 3;
and digit 2. The common reflected output heights for original rows
0, 1 and 2 are respectively 5, 4 and 3. Every original of q-height
at least two keeps its literal strip and remains q-bearing.

Since $n\ge83$, WR7 gives

$$
N_2\le1,
\qquad
N_0\ge64,
\qquad
N_2=1\Longrightarrow N_0\ge73.
\tag{WR8}
$$

Thus the exchange forces bottom-row originals specifically
at q-height one in at least 64 distinct moving colors. The numerical
parents are actual q-free originals. These are global counts, not
additional terms to add to the 471-owner inventory of one specified
masked component.

## The actual pure guards reduce the selector domain to 135 words

The original numerical labels 3 and 9 are present. Their actual
classes are disjoint: if the phase of the 9-class agreed with the
phase of the 3-class modulo 3, deleting the 9-class would preserve
whole coverage and contradict count-minimality. Write their forbidden
digits as $d_0=\alpha$ and $(d_0,d_1)=(\beta,\gamma)$, respectively,
where $\beta\ne\alpha$.

Both classes are retained among the q-free originals. An integer
uncovered by that retained family therefore has a word in

$$
\mathcal S=\{(d_0,\ldots,d_4):d_0\ne\alpha,
                    \ (d_0,d_1)\ne(\beta,\gamma)\},
\qquad |\mathcal S|=5\cdot27=135.
\tag{WR9}
$$

The set $\mathcal S$ is an enclosing domain for the actual residual;
it need not equal that residual. Coverage by selectors is needed
only on this domain. All other integers are already covered by the
retained guards.

A type-2 selector fixes $d_2$ and contains 45 safe words. There are
three disjoint such cells. Within one of these cells, a type-1
selector fixes $(d_1,d_3)$. The six choices with $d_1\ne\gamma$
each contain six safe words, and the three choices with
$d_1=\gamma$ each contain three. This accounts for all 45 words.

Let $t=N_2\le1$, using WR8, and choose all t type-2 colors on
different top cells. Among the remaining cells there are
$18-6t$ type-1 cells of size six. Assign

$$
k=\min(N_1,18-6t)
\tag{WR10}
$$

distinct type-1 colors to that many cells. These selections cover
$45t+6k$ safe words. If there are at least $135-45t-6k$ remaining
colors, assign one distinct remaining color to each uncovered word,
using that word as its seed. Every selector matches its own seed,
regardless of its type. Its actual selector may also cover other
words; no claim that it has been reduced to a singleton is needed.

Consequently, complete safe-domain selectors exist whenever

$$
n+44t+5\min(N_1,18-6t)\ge135.
\tag{WR11}
$$

Use the same original strips and reflected output labels as WR4.
For every integer, first test the retained q-free family. Only an
uncovered integer needs the safe-domain selector and the complete
color source. Numerical distinctness, legality and the strict count
decrease are unchanged. Count-minimality rules out WR11, so its
left side is at most 134.

Because $n\ge83$ and $t\le1$, the truncated case
$N_1\ge18-6t$ would already violate this upper bound. Hence the
minimum in WR11 equals $N_1$, giving the joint necessary inequality

$$
\boxed{N_0+6N_1+45N_2\le134.}
\tag{WR12}
$$

Together with $N_0+N_1+N_2=n\ge83$, this implies

$$
\boxed{N_0\ge73,\qquad
N_2=1\Longrightarrow (N_0\ge81\ \text{and}\ n\le90).}
\tag{WR13}
$$

These are restrictions on actual height-one owners in the same
global cover. They do not assert that their cofactor phases coincide
or that they admit one common repair.

## Two height permutations retain the full height-one row mask

For each bottom-serving color c, let $R_c$ be the set of ternary
rows of **all** its actual q-height-one originals. This set contains
zero. Write $B_0,B_{01},B_{02},B_{012}$ for the numbers of colors
whose exact sets are respectively $\{0\},\{0,1\},\{0,2\},\{0,1,2\}$.
Then

$$
B_0+B_{01}+B_{02}+B_{012}=N_0.
\tag{WR14}
$$

The deeper originals do not enter this classification and continue
using their literal strips.

The numerical height assignment need not be the reflection $5-a$.
Choose one permutation $\pi$ of the output heights $3,4,5$, indexed
by original rows $a=0,1,2$. A selected height-one original with
cofactor m now receives the label $3^{\pi(a)}m$. Preserve its old
low a digits and fill digits a through $\pi(a)-1$ from its color's
seed. This is the same CRT enclosure construction. The new height
recovers a because $\pi$ is injective; all new heights exceed two,
and unchanged deeper strips remain q-bearing. Thus the whole output
family still has distinct odd nonunit labels.

For a bottom-serving color, use the prefix depth
$E_c=\max\{\pi(a):a\in R_c\}$. For every other moving color use
$E_c=5$. A selector fixing the first $E_c$ digits supplies every
required block for that color's height-one originals. A conflicting
old low-digit condition only makes the inverse empty; it does not
invalidate its enclosure.

Within the safe domain WR9 there are five complete low-two-digit
roots, with 27 extensions each. Prefix depths 3, 4 and 5 therefore
have respectively 9, 3 and 1 safe leaves. Process the colors by
increasing depth, assigning disjoint cells. At each stage the
unfilled cells subdivide into three cells at the next depth. Hence
weight at least 135 supplies complete selectors, using each selected
color once. The same retained-family-first argument and the omitted
original q give a strictly smaller whole cover, which is forbidden.

For $\pi=(3,4,5)$ the four bottom-mask weights are $9,3,1,1$;
for $\pi=(3,5,4)$ they are $9,1,3,1$. Every nonbottom color contributes
an available singleton prefix in both constructions. Applying
count-minimality to these two comparison covers separately gives

$$
\boxed{n+8B_0+2B_{01}\le134,\qquad
       n+8B_0+2B_{02}\le134.}
\tag{WR15}
$$

Both inequalities constrain the same original counts. Their proof
does not require simultaneously executing the two comparisons.

Since $n\ge83$, each inequality implies
$4B_0+B_{0j}\le25$. Combining them with WR14 gives
$B_{012}\ge N_0+7B_0-50$. In particular WR13 yields

$$
\boxed{B_0\le6,\qquad B_{012}\ge23+7B_0.}
\tag{WR16}
$$

Thus at least 23 actual colors each contain height-one originals in
all three ternary rows. Within one such color these originals need
not share a cofactor or a cofactor phase. The conclusion does not
supply a same-cofactor triple or a joint repair.

## One pure replacement excludes colors supported only at the top row

Assume, in addition to the actual pure 3 and 9 guards and q original,
that the same family contains the original 3q. The argument in this
section needs class-count minimality and at least 82 moving colors;
it does not use modulus-sum minimality. Presence of 3q is an explicit
input to the exact application. Under the full EB1 branch at q=113,
its ordinary supplier is SC460 together with divisor closure.

Every moving color then has an actual height-one owner below the top
ternary row:

$$
\boxed{\forall c\in U,\quad
\exists i:\ j_i=1,\ c_i=c,\ a_i\le1.}
\tag{WR17}
$$

In the minimum-row notation of WR7 this says $N_2=0$. It asserts a
witness separately for each color, with that owner's literal cofactor
phase; it does not identify the cofactors or phases of different colors.

Suppose instead that all height-one owners of one color c have row two.
Use the same global reflected labels $3^{5-a_i}m_i$ as WR4, and retain
the literal strips of selected deeper originals. Give c the selector
whose third ternary digit is zero. It contains 45 of the 135 safe
length-five words. Choose any safe old word w modulo 9 and add one pure
class

$$
x\equiv w+9\pmod{27}.
\tag{WR18}
$$

Its third digit is one, so its nine safe length-five words are disjoint
from c's selector. Exactly 81 safe words remain. Assign these words to
81 other moving colors, using a full length-five selector for each.
This is possible when $|U|\ge82$. Additional moving colors may receive
arbitrary seeds. All choices are fixed once for the whole replacement.

For any output outside the retained q-free originals, the actual pure
guards place its ternary word in this safe domain. The extra pure class
covers its own cell. Every other word has at least one selected color; the
complete literal-strip source for that color supplies an actual original
owner. The reflected enclosure then covers the output. The distinguished
color uses new height three because each of its height-one owners has old
row two. Every singleton selector satisfies the enclosure condition for
all three old rows. The whole old modulo-nine and cofactor coordinate
is preserved before choosing an owner.

WR4's global row assignment preserves numerical distinctness among
selected owners. The extra modulus 27 is fresh: retained originals have
ternary height at most two; reflected moving originals have nonunit
cofactor and new ternary height at least three; deeper strips remain
q-bearing. Every new modulus is an odd nonunit.

Delete all q-bearing originals. Each selected original produces one
class, even when its selector intersection is empty. The actual q and
3q originals have unit cofactor, so neither has a moving color and
neither is selected. There are therefore at least two deleted originals
without selected replacements, while WR18 adds only one class:

$$
K'\le K-2+1<K.
\tag{WR19}
$$

This contradicts class-count minimality and proves WR17. The argument
uses the complete deletion hole; it does not claim that the extra pure
class alone covers either charged original's former territory.

## Reuse and boundary

This construction reuses complete-color stripping, CRT enclosure,
and the numerical height recovery of Report385 HPA6--HPA8. Restricting
the coding domain by retained pure guards reuses Report385 GHA1--GHA5.
The selector allocation is a finite prefix packing. The additional
interface is the common reflection WR4 on height-one originals together
with unchanged strips of all deeper originals; the existing component
exchanges do not already check that combination.

The general-p construction is an ordinary mathematical derivation.
The exact ternary consumer has a cache-guarded Lean application. It
starts with the actual whole integer cover, distinct odd nonunit
labels, global count-minimality, ternary height at most two, and the
actual original label q. It derives full global color-strip service,
the existence of height-one owners, and their minimum rows. No
component, common private point or CD21 inventory is assumed.

The application constructs the finite selectors, the actual CRT
classes and their numerical labels, checks whole integer coverage
and global injectivity, and uses the unselected original q for strict
count decrease. Its final consumer derives WR7--WR8 with actual
height-one witnesses at each counted minimum row. The application
exits successfully with 169 axiom-closure reports, each using only
`propext`, `Classical.choice`, `Quot.sound`, or no axioms; there are
no errors or `sorryAx`.

The safe-domain extension additionally takes the actual original
labels 3 and 9. It derives their phase incompatibility from the same
count-minimality assumption, constructs the 135-word allocation, and
checks the retained-family-first whole-coverage argument. Its final
consumer derives WR12--WR13 together with the actual minimum-row
witnesses and WR7. This extended application exits successfully with
183 axiom-closure reports: 177 use only the same three standard axioms
and six use no axioms. It has no errors or `sorryAx`. The general-p
statement WR6 remains outside this ternary application.

The two height permutations and exact row-mask consumer also have a
complete cache-guarded application. It starts with the same actual
cover, q, 3 and 9 originals, class-count minimality and $n\ge83$.
The row masks are extracted from all actual height-one owners. It
derives WR15--WR16 after constructing both comparison families and
checking each against the same original family. The application
exits successfully with 212 axiom-closure reports: 203 use only
standard axioms and nine use no axioms, with no errors or `sorryAx`.

The one-pure-replacement application additionally takes the actual
original label 3q and uses only class-count minimality. With at least
82 moving colors it constructs the 45-word selector, one fresh pure
27-class and the remaining 81 singleton selectors, preserving whole
coverage and distinct labels. Its final consumer proves WR17, with
an actual height-one owner in row zero or one for every moving color.
The application exits successfully with 218 axiom-closure reports:
209 use only standard axioms and nine use no axioms, with no errors
or `sorryAx`.

For the stronger EB1 assumptions of the research branch, reuse
[Report388, SC468](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment)
before treating WR13 or WR16 as the best available bounds. At q=113,
SC440 and SC460 supply the full five-word projection and, with divisor
closure, the actual q, 3q and 9q donors. SC468 supplies an actual
height-one divisor triple in every admissible six-color selection,
with specified ternary tests. The full moving set
U avoids all three unit-cofactor donor digits, so any six of its
colors are admissible, using a fixed safe word. Six colors missing
any one height-one row would contradict that result. Thus each row
is missing from at most five colors, giving $N_0\ge n-5\ge78$ and,
by the union bound, at least $n-15\ge68$ colors containing all three
rows. These consequences reuse SC468; they are not new inventory
results. SC468 uses modulus-sum minimality as well as class-count
minimality.

The same argument also applies to the larger set V of all 113 digits
except the actual q and 3q first digits. Those digits are distinct,
so $|V|=111$. Choose one safe word different from the actual 9q
word; using it for every selected color satisfies the final-donor
exception even when its first digit lies in the six-set. Each row
therefore occurs at height one in at least 106 colors of V, and at
least 96 colors of V have owners in all three rows. These counts
concern actual height-one owners; different rows at a fixed color
need not have the same cofactor. V and the moving set U are
different domains, so these counts are not added.

A complete cache-guarded application verifies the q=113 SC468
exchange and this full-V consequence. Its hypotheses are the actual
whole integer cover, count-then-modulus-sum minimality, the displayed
factorization with row at most two and arbitrary finite q-height,
and the actual 3, 9, q, 3q and 9q original labels. The six-color
consumer constructs one common source preserving the full old
modulo-nine and W-coordinates, proves coverage by all replacements,
and checks grouped payment and numerical distinctness. It retains
the full permitted six-set and the exact 9q word exception. The
final consumer derives $|V|=111$, the row bounds 106 and the
three-row bound 96 directly from these original inputs. The
application exits successfully with 271 axiom-closure reports:
262 use only standard axioms and nine use no axioms, with no errors
or `sorryAx`. This does not verify the other prime instances or
the later probability and cell-count deductions in Report388.

These are transient applications of existing coordinate, CRT and
finite-cardinality machinery, with the three-row arithmetic checked
explicitly. No new frozen Lean declaration or coverage claim is
retained. The constraints do not themselves supply a complete repair
for an arbitrary multi-parent color family, and unrestricted
Erdős #7 remains unresolved.
