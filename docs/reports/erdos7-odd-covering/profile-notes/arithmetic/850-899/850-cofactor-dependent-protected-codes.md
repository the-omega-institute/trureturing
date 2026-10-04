[Index](../../../marked_head_profile.md) · [Grouped shallow slots](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment)

# Cofactor-dependent codes with protected owner subtrees

Keep the original EB1 family, $H_3=2$,
$q\in\{101,103,107,109,113\}$, $r=(125-q)/2$, and
$Q=9q^GW$ with $(W,3q)=1$ from [Report 388, Section 74](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment). A first-digit
code can depend on a retained cofactor coordinate without
splitting its original inverses if every moving digit subtree
has only owners that fix that coordinate. The construction
below gives a phase-sensitive obstruction and a moment under
one simultaneous code law. The divisor-controlled construction does
not supply its required movable-digit inventory. The component
construction below obtains at least 83 movable digits under the
additional GHA11 height envelope, but supplies no contradictory
upper bound on actual component profiles.

All SC labels below refer to Report 388. Use its terminal
digits $\alpha,\beta,\gamma$, and write
$c_a(m)=\rho_{3^aqm}\bmod q$,
$b_m=\rho_{3qm}\bmod3$, and $z_m=\rho_{9qm}\bmod9$.

The source-constancy principle is the one in
[Report 375, LA2--LA3](../350-399/375-deep-prime-prefix-projections-and-tree-contraction.md).
The independent-row failures in
[Report 385, Sections 99 and 101](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md)
require a common code with complete original inverses. The
group payment and full-hole coverage here use SC466--SC472;
the alternative enclosure test uses the actual-phase hull
condition SC130--SC132. An occupied-label window alone gives
no count or sum saving, as in Report 385, Section 197.

## Movable digits and one complete source

Write every actual q-bearing original as

$$
d_i=3^{a_i}q^{e_i}m_i,\qquad
0\le a_i\le2,\quad e_i\ge1,\quad(m_i,3q)=1,
\qquad c_i=\rho_i\pmod q.
$$

Fix $h>1$ with $h\mid W$, and define

$$
D_h=\left\{c\in\mathbb F_q:
\text{every actual q-bearing original with }c_i=c
\text{ has }h\mid m_i\right\}.
\tag{CD1}
$$

The quantifier covers all q-heights and all three ternary
heights. For every digit outside $D_h$, protect its entire
continuing inverse subtree, including every later-digit
dictionary, from changes between control rows. In particular
$\alpha,\beta,\gamma$ are protected: their actual owners
$q,3q,9q$ have cofactor one, and $h>1$. For an empty owner
set the universal condition is vacuous. In the present cover,
the nonempty deletion hole and original whole coverage supply
an owner at each first digit.

Fix one geometric initial forest from Report 388, Section 74, with its
q and 3q terminal leaves, exactly $r$ short continuing leaves
of depth four, and all other continuing leaves of depth five.
Fix the later-digit encoding on each geometric leaf. Complete
every terminal path to a q-word of length $G$ with a fixed
suffix, keeping these complete paths fixed across control rows.
If $|D_h|\ge r$, reserve all short leaves and $|D_h|-r$
long leaves as one movable block. Assign the protected
continuing digits to the other long leaves.

For each $t\in\mathbb Z/h\mathbb Z$, permute only the
labels in $D_h$ on that same movable block. Every row is
therefore a complete bijection on the same initial leaves;
the protected subtrees and both terminal paths stay fixed.
On the entire corridor
$\mathcal A\times\mathbb Z/W\mathbb Z$, define the source
before choosing any original owner by

$$
\begin{aligned}
\operatorname{source}(x)
 &\equiv\theta_{x\bmod h}(x_{3\text{-digits}})
       &&\pmod{q^G},\\
\operatorname{source}(x)&\equiv x&&\pmod{9W}.
\end{aligned}
\tag{CD2}
$$

Here $\theta_t$ is the complete q-word from row $t$.
The common output carrier $3^{3G+2}W$ still suffices.
For any actual original $i$, there are two cases. If
$h\mid m_i$, its preserved literal $m_i$-phase fixes the
entire control row. Its continuing inverse uses that fixed
row and is empty or one whole arithmetic progression with
its own $m_i$-phase. If $h\nmid m_i$, CD1 protects
$c_i$ and its entire inverse subtree. Its inverse is again
empty or one whole progression, without an extra h-condition.

This argument covers all $e_i\ge1$. Protecting only the
first digit, while changing its later dictionary, would not
suffice at greater q-height. When a movable first digit has
a short leaf in one row and a long leaf in another, its
owner fixes the row. The respective 81-way and 27-way
continuations both reach depth eight at the second q-level;
deeper nonempty inverses retain depth $3e_i+2$.

## The complete grouped payment

For each $m>1$, group the available actual shallow originals
$qm,3qm,9qm$ by their common $(3q)$-free cofactor. Let
$I_m\subseteq\{0,1,2\}$ index their nonempty continuing
inverses, and put $k=|I_m|$. If $k\le2$, assign the lowest
$k$ labels among $27m,81m,243m$. If $k=3$ and at least one
inverse is long, assign $243m$ to a long inverse and the
other two labels to the remaining inverses. As in SC471,

$$
\begin{aligned}
\sum_{\text{new shallow group}}M
 &=27m\frac{3^k-1}{2}\\
 &\le\frac{27}{q}\sum_{a\in I_m}3^aqm
 <\sum_{a\in I_m}3^aqm\qquad(k>0).
\end{aligned}
\tag{CD3}
$$

Different members of the same group may use different
control rows and different literal $m$-phases. Each still
receives one global enclosure of its own inverse, so the
joint comparison CD3 requires no agreement of those phases.
Empty inverses cost no replacement. The actual terminal
donors retain labels 27 and 81. The protected $\gamma$
subtree keeps any continuing $9q$ inverse long, allowing
label 243; if $\gamma=\beta$, that inverse is empty.
Every deeper original retains label $3^{3e+a}m$ and its
strict contraction from Report 388, Section 74.

There is at most one candidate per deleted original. Shallow
ternary exponents 3, 4, 5 are disjoint from the deep exponents
$3e+a\ge6$ and the retained exponents at most two. Distinct
$(3q)$-free cofactors cannot give equal new numerical labels,
and the deep decoder still recovers $e,a,m$. Thus all new
labels remain distinct odd nonunits.

Source CD2 preserves the entire old $(\bmod9,W)$
coordinate. For an output in the complete deletion hole,
its full source therefore lies in the same hole. Original
whole coverage supplies a deleted owner after the source has
been selected. Terminal outputs are covered by the terminal
donors; a continuing output belongs to its owner's complete
inverse and assigned enclosure. Retained q-free originals
cover outside the hole. Consequently, if no group has three
nonempty short inverses, this one replacement family satisfies
$K'\le K$ and $\Sigma'<\Sigma$, contradicting EB1.
Every feasible simultaneous row code must therefore have an
actual all-short triple.

## Disjoint short-digit sets for control colors

Let $T_h$ be the residues modulo $h$ missed by all actual
original classes of nonunit modulus dividing $h$. These are
retained q-free originals. An actual q-bearing original with
$h\mid m_i$ has its h-phase in $T_h$: otherwise an actual
proper ancestor contains it, contradicting irredundancy.

Choose a coloring $\chi:T_h\to\{1,\ldots,B\}$. Use the
same row code on all residues of each color. Outside $T_h$,
choose any row permutation respecting the protected subtrees.
If

$$
|D_h|\ge rB,
\tag{CD4}
$$

choose disjoint r-element sets $R_1,\ldots,R_B\subseteq D_h$.
In color $j$, assign $R_j$ bijectively to the common short
leaves and complete the remaining movable labels on the long
leaves. This constructs one compatible code on all rows.

For a candidate actual triple $qm,3qm,9qm$, first require
all three $c_a(m)$ to lie in $D_h$. Then CD1 gives
$h\mid m$, so its actual phases
$t_a=\rho_{3^aqm}\bmod h$ lie in $T_h$, where
$j_a=\chi(t_a)$ is defined. All three inverses can be short
only if $c_a(m)\in R_{j_a}$, along with their literal
middle-root and final-word tests. Disjointness of the sets gives

$$
\boxed{c_a(m)=c_b(m)\quad\Longrightarrow\quad
\chi(t_a)=\chi(t_b)
\quad\text{for every all-short obstruction}.}
\tag{CD5}
$$

Thus a $C_1$ triple whose three control phases do not share
a color cannot obstruct this exchange. This uses the three
actual phases separately; it assumes no common point of their
cofactor sections.

For $h=p$, the actual p-class removes one row and
$|T_p|=p-1$. Singleton colors require
$|D_p|\ge r(p-1)$. Under this inventory condition, every
legal simultaneous code has an actual all-short triple whose
p-phases agree on each repeated-q-digit block. The surviving
types are $C_1$ with three equal p-phases, $C_{2A}$ or
$C_{2B}$ with equal p-phases on the repeated pair, and $C_3$.
The third owner of a $C_2$ triple may have another q-digit
and another p-phase. A sufficient descent hypothesis must
exclude all of these surviving types in the chosen code.

SC483 does not itself exclude equality after reduction modulo
$p$. For example, $0,1,6,11$ are distinct modulo 25, while
the three descendant phases $1,6,11$ all equal 1 modulo 5.

For $h=p^b$, a movable actual owner and divisor closure
supply the actual pure powers $p,\ldots,p^b$. Their classes
are pairwise disjoint by comparable-original irredundancy.
They remove exactly $\sum_{a=1}^b p^{b-a}$ rows, giving

$$
|T_{p^b}|=p^b-\sum_{a=1}^b p^{b-a}
        =p^b-\frac{p^b-1}{p-1}.
\tag{CD6}
$$

At $h=25$, there are 19 legal rows. Nine pairs and one
singleton give $B=10$, so at $q=113$, $r=6$, CD4 requires
60 movable digits. Separating all 19 rows would require 114.
Every $C_1$ triple with three distinct phases modulo 25 is
eliminated because no color contains three rows. In particular,
SC483 gives that separation for a potentially active $m=25$
$C_1$ group. For larger $m$, distinct phases modulo $m$
need not remain distinct modulo 25. The actual inventory bound
$|D_{25}|\ge60$ has not been deduced from EB1.

## A simultaneous-code moment at q equal to 113

Fix $h$, $\chi$, $B$, and $D=|D_h|\ge6B$. Choose one
word $z$ uniformly from the five safe words, and place all
six short leaves above $z$. The terminal packing in Section
74 permits this, since six of the nine depth-four slots are
used above $z$. For each sampled $z$, fix one such geometric
forest and protected subtrees across all control rows.

Uniformly inject all $6B$ labeled color slots into $D_h$.
The six slots of color $j$ give its set $R_j$, and these
sets are disjoint. Complete each color's permutation on the
remaining movable leaves. Together with the fixed terminal
paths and protected subtrees, each outcome is one lawful
code with source CD2.

For an actual cofactor triple $m$, give its event probability
zero unless all three digits lie in $D_h$, $z_m\in\mathcal A$,
$b_m\equiv z_m\pmod3$, and each repeated digit has a
consistent color demand as in CD5. If those tests pass,
let $d_m$ be the number of distinct digits among the three
$c_a(m)$, and let $n_{m,j}$ count the distinct digits demanding
color $j$. Its exact all-short probability is

$$
P_m=\frac15\,
\frac{\prod_j(6)_{n_{m,j}}}{(D)_{d_m}},
\qquad (x)_k=x(x-1)\cdots(x-k+1).
\tag{CD7}
$$

The factor $1/5$ is the one common choice $z=z_m$, with
the middle-root test checked against that same word. For each
color, the numerator counts distinct short slots for its
demanded digits. Completing one injection of all color slots
gives the denominator; choices for different rows or cofactors
are not being treated as independent. Every sampled code has
an actual obstruction by the paid exchange above, so linearity
of expectation gives

$$
\boxed{\sum_{\substack{\text{actual triples }m>1\\(m,3q)=1}}
P_m\ge1.}
\tag{CD8}
$$

$C_1$ groups with phases in different colors have zero
probability, as do $C_2$ groups whose repeated pair demands
different colors. Eligible $C_1$ groups within one color
retain probability $6/(5D)$. Distinct-digit groups remain,
with the weights in CD7. This moment requires its own
actual inventory and coefficients; substituting these values
into SC480 without rebuilding that inventory is not justified.

For $h=25$, additionally choose the nine pairs and singleton
uniformly, independently of the slot injection. A $C_1$
group with three distinct control rows has probability zero.
With exactly two distinct rows, those rows share a color with
probability $(17/19)(1/17)=1/19$: the singleton must avoid
the specified pair, and the remaining matching must join it.
With only one distinct row, monochromaticity is automatic.
Subject to the same ternary and digit eligibility tests, the
three respective probabilities are therefore
$0$, $(1/19)\,6/(5D)$, and $6/(5D)$.

## Full cofactor gcds and the complete-inverse hull boundary

For each first digit, define

$$
g_c=\gcd\{m_i:c_i=c,\ e_i\ge1\},
\qquad g_c=W\text{ when the owner set is empty}.
\tag{CD9}
$$

If the entire inverse subtree of $c$ depends on the retained
W-coordinate only through its residue modulo $g_c$, every
owner fixes that dependency and no inverse splits. The
subtrees must still form one compatible code at each W-point.
One sufficient realization uses disjoint digit blocks, each
controlled by a common divisor of all $g_c$ in that block,
and permutations within those blocks on one fixed forest.
The disjoint permutations compose to a pointwise bijection.
CD1 is the single-block specialization.

A two-digit transposition of $c,d$ obeying both owner
restrictions can vary only modulo $\gcd(g_c,g_d)$; both
periods divide $W$, so invariance under them implies
invariance under their gcd. Coprime values force a constant
switch. More general coupled permutations are not classified
by this observation. To obtain a paid whole-cover exchange,
the actual donor leaves and their complete terminal paths
must also stay fixed, the continuing unit-cofactor $9q$
inverse must remain long, and all the count, sum, collision,
and coverage obligations above must hold.

If owner constancy is relaxed for a shallow group, collect
all row pieces of each original inverse before computing its
common congruence hull, retaining its literal $m$-phase. A
new enclosure label is legal only if it divides that complete
inverse hull. For $k$ nonempty shallow inverses, let
$H_{(1)}\le\cdots\le H_{(k)}$ be the sorted ternary hull
heights. The inequalities $H_{(j)}\ge j+2$ allow distinct
labels $3^3m,\ldots,3^{k+2}m$ and the payment CD3.
This is a sufficient test for one shallow group. It does not
give a whole-family descent when other inverses may split.
Every deep original still needs a paid enclosure, for example
a complete-inverse hull divisible by its prescribed
$3^{3e+a}m$, and all terminal, coverage, count, sum, and
global collision obligations remain. Every extra progression
requires its own payment.

## An exact failure of unrestricted control-row switching

Take $q=113$, control prime 5, and cofactor $m=7$.
Use safe words $\{0,1,3,4,6\}$, terminals $[4]_{27}$
and $[3]_{81}$, six short leaves $[9j]_{81}$ for
$0\le j<6$, and every remaining depth-five leaf in the
safe corridor. These form 113 leaves. Assign terminal
digits 0 and 1, assign digits 2 and 3 to
$S=[0]_{81}$ and $T=[1]_{243}$ respectively, and assign
the other digits bijectively to the remaining leaves.
On every nonzero row modulo 5, swap only digits 2 and 3;
on row zero leave them fixed. Each row is still a complete
leaf-to-digit bijection.

Use one CRT source that preserves $9\cdot5\cdot7$ and
has q-digit given by this row code. The test original
$[567]_{791}$ has q-digit 2 and 7-phase zero. It does not
fix the switching coordinate. Its complete continuing inverse is

$$
\begin{aligned}
&\{x:x\equiv0\pmod7,\ x\equiv0\pmod{81},\
                 x\equiv0\pmod5\}\\
&\quad\cup
\{x:x\equiv0\pmod7,\ x\equiv1\pmod{243},\
                 x\not\equiv0\pmod5\}.
\end{aligned}
\tag{CD10}
$$

In period 8505, the inverse points are exactly
$0,973,2674,2835,5670,6076,7777$. Their common congruence
hull is 7, so no single label $3^j\cdot7$ with $j\ge1$
encloses the inverse. Two enclosures, $[0]_{189}$ and
$[406]_{567}$, suffice. Their label sum is $756<791$, but
their count is two instead of one. Without a spare deletion
credit this is not an EB1 descent. Adding the control-prime
condition can create more components and repeated numerical
labels; it supplies no count credit.

This is a partial original test against a complete code,
not a whole EB1 covering realization or an Erdős #7
counterexample. It refutes the assertion that valid codes
on every control row automatically preserve one payable
progression per original. A larger paid packet or another
source remains possible.

## Codes constant on actual owner components

The full numerical gcd in CD9 is one sufficient control. Actual phases
permit another: keep each moving subtree constant on every actual
owner's entire cofactor cylinder. This section uses the same one EB1
whole cover, $q=113$ and $H_3=2$, with all original q-heights retained.

Let $P$ be the set of first q-digits of **all** unit-cofactor originals
$3^a q^j$, with $0\le a\le2$ and $1\le j\le G$. Fix
$U\subseteq\mathbb F_{113}\setminus P$, and write $n=|U|\ge6$.
Every digit outside $U$ has a protected complete subtree, including
its later dictionaries and any terminal path. Taking the whole
complement gives $n\ge113-3G$. Only under the additional GHA11
height bound $G\le10$ does this imply $n\ge83$; a bound on the
prime support alone does not imply that height bound.

The vertices of the owner graph are all actual originals
$3^{a_i}q^{e_i}m_i$ with first q-digit $c_i\in U$. In particular,
the graph includes every ternary row and every q-height. Join distinct
vertices when their full literal cylinders

$$
C_i=[\rho_i]_{m_i}\subseteq\mathbb Z/W\mathbb Z
$$

intersect. For each graph component $C$, let $V_C$ be the union of
its cylinders. Distinct $V_C$ are disjoint: a shared point would give
an edge between their components. Every $C_i$ lies wholly in its
component's $V_C$. Consequently a permutation fixed on $V_C$ is
fixed on every moving owner's entire cylinder. No common numerical
divisor or congruence-coset shape of $V_C$ is assumed.

Including a unit-cofactor owner would give a cylinder equal to all
of $W$, merging the entire graph into one component. Its exclusion
is therefore substantive; a deep unit owner cannot be silently
dropped from the graph.

### One simultaneous component code

Choose one global safe word $z$ uniformly from the five safe words.
For every possible $z$, fix a lawful forest with all six short leaves
above $z$. Such a forest exists: the actual $3q$ root has at least
two safe words, so place its depth-four terminal over a different
word $v$; place the q-terminal over a word different from both $v$
and $z$. All nine depth-four slots over $z$ are then available for
the six short leaves. The remaining safe leaves give 105 long leaves.

Fix the protected continuing digits at long leaves and the two
terminal digits at their terminals. If $\gamma$ is nonterminal,
give it any fixed long leaf; its actual $9q$ continuing inverse is
long or empty. There are $111-n$ protected continuing digits, so
$n\ge6$ leaves exactly enough room to reserve a moving block of
six short leaves and $n-6$ long leaves. The case $n=111$ is allowed
when the actual unit-digit set has only the two terminal digits.

Independently for every component $C$, choose a uniform bijection
from $U$ to this same moving block, and use it at every point of
$V_C$. Outside their union use a fixed bijection. For each global
$z$, the protected subtrees, terminal suffixes and later dictionaries
on the geometric leaves are fixed across all component rows.

This defines one source on the complete corridor before choosing an
original owner: decode the full q-word using the row of its actual
W-coordinate and preserve the complete modulo-$9W$ coordinate.
The common carrier $3^{3G+2}W$ suffices. A moving owner fixes its
row on its whole $m_i$-cylinder; every other owner has a protected
subtree. Every continuing inverse is therefore empty or one whole
AP with its original cofactor phase, at every q-height. No additional
component mask restricts that AP, because the entire original cylinder
already belongs to that component.

The grouped allocation CD3 now applies without requiring the three
phases of one numerical cofactor to belong to the same component.
The terminal and deeper payments, distinct fresh numerical labels
and whole-source coverage are those already checked above. If no
group were bad, this would be one EB1-improving whole replacement.
Hence every outcome of this experiment has an actual all-short triple.

This uses the all-six-above-one-word geometry. It does not preserve
Report858's distinct selected modulo-27 parents, short-owner
inertness or balanced-parent Hall estimates.

### An exact component-weighted moment

For a nonunit cofactor $m$ with $9qm$ original, let $c_0,c_1,c_2$
be its three actual shallow first digits and $\kappa_0,\kappa_1,
\kappa_2$ their owner components. First require all three digits to
belong to $U$, the actual $9qm$ word $z_m$ to be safe, and the
actual $3qm$ root $b_m$ to satisfy $b_m\equiv z_m\pmod3$.
Otherwise its bad-event probability is zero. For an eligible group put

$$
r_{m,C}=\left|\{c_a:a\in\{0,1,2\},\ \kappa_a=C\}\right|,
\qquad (x)_r=x(x-1)\cdots(x-r+1).
$$

Repeated equal digits within a component are counted once. The exact
bad-event probability and necessary whole-cover inequality are

$$
p_m=\frac15\prod_{C:r_{m,C}>0}
       \frac{(6)_{r_{m,C}}}{(n)_{r_{m,C}}},
\qquad
\sum_m p_m\ge1.
\tag{CD11}
$$

The factor $1/5$ selects the one global word $z=z_m$. Within each
component the short digits are a uniform six-subset of $U$; the
inclusion probability of $r$ distinct specified digits is
$\binom{n-r}{6-r}/\binom n6=(6)_r/(n)_r$. Different components
have independent permutations. Different groups use those same
permutations and are not assumed independent. Every outcome has a
bad group, so expectation and the finite union bound give CD11.

Write $f_r=(6)_r/(n)_r$. Let $A_1,A_2,A_3,A_{11},A_{21},A_{111}$
count eligible groups whose multisets of positive $r_{m,C}$ are
$(1),(2),(3),(1,1),(2,1),(1,1,1)$, respectively. These six cases exhaust
the three actual shallow owners. Then CD11 is equivalently

$$
f_1A_1+f_2A_2+f_3A_3+f_1^2A_{11}
       +f_2f_1A_{21}+f_1^3A_{111}\ge5.
\tag{CD12}
$$

A repeated-digit triple in $k$ components has probability
$(6/n)^k/5$. Splitting these three phases across components reduces
that probability. There is no monotonic gain for all groups: for
three distinct digits the factor $(6/n)^3$ from three components
is greater than $(6)_3/(n)_3$ from one component when $n>6$.
CD12 cannot be substituted into SC480 while keeping its code law
or its original coefficients.

### Whole coverage gives every component all moving digits

Choose an original in a nonempty component and one of its complete
private points $x$. For each $c\in U$, change only the first q-digit
of $x$, preserving all higher q-digits, its complete ternary word
and W-coordinate $w$. Every q-free original still misses. Whole
coverage supplies a q-bearing owner with first digit $c$, hence a
vertex of this graph. Its cylinder and the initial owner's cylinder
both contain $w$, so the new owner lies in the same component.
Distinct digits have distinct owners. Every component therefore has
at least $n$ vertices, realized at this one actual cofactor point.

This gives no upper bound on component size or count. SNC1 controls
top originals at one fixed ternary word, first q-digit and cofactor
point; the component graph includes all rows and permits paths through
different cofactor points. A pointwise incidence bound cannot be
used as a component-size bound.

Nor does the original every-code/exists-bad-group statement supply
a code-independent cofactor law. Conditioning on each code's complete
unpaid region can produce a legitimate joint law whose cofactor
marginal depends on the code. Bare SC479 probabilities cannot then
be multiplied by separately selected incidence masses. The complete
joint-hole constructions in Report385 sections 139 and 143 retain
this dependence. CD11 gives lawful adaptive codes, not the missing
uniform law or a strict reverse inequality.

### Components of the full preserved-coordinate supports

The component construction can also preserve each owner's ternary
test before deciding which code row to use. Let $\mathcal A$ be the
five safe words modulo 9. For every moving owner define

$$
R_i=\{(u,w)\in\mathcal A\times\mathbb Z/W\mathbb Z:
u\equiv\rho_i\pmod{3^{a_i}},\quad
w\equiv\rho_i\pmod{m_i}\}.
\tag{CD13}
$$

Use all original q-heights and all three ternary rows, and join two
owners when their full $R_i$ supports intersect. Every moving owner
has a nonempty support: its complete private point misses the retained
pure 3 and 9 classes and therefore has a safe old word. Distinct
component unions are disjoint, and the whole support $R_i$ belongs
to its component $\kappa_i$. These components refine the W-only
components because every support intersection projects to a cofactor
cylinder intersection.

For one global safe word $z$, use the same fixed forest and protected
subtrees as above, and choose an independent moving-block permutation
for each of these finer components. For an output $x$, select its row
from the component containing $(x\bmod9,x\bmod W)$, using a fixed
row off the component unions. Decode its complete q-word using that
row and preserve $x\bmod9W$. This defines one total source on the
whole corridor before an original owner is selected.

At fixed $w$, different old words can use different rows. The labels
obtained by evaluating all geometric leaves need not form one global
bijection. The argument consequently uses the following direct
whole-inverse identity, rather than identifying the construction with
SC468's originally stated code class. Write $\theta_C$ for the
complete fixed-row decoder of component $C$. The complete continuing
inverse of a moving owner is exactly

$$
I_i=\{x\text{ continuing}:
(x\bmod9,x\bmod W)\in R_i,\quad
\theta_{\kappa_i}(x)\equiv\rho_i\pmod{q^{e_i}}\}.
\tag{CD14}
$$

Membership of the actual source in owner $i$ first forces the
preserved pair to lie in $R_i$, which already forces its row to be
$\kappa_i$. This proves both directions of CD14. For the fixed
decoder, the q-prefix inverse is empty or one ternary prefix
progression, of depth four or five at q-height one and depth
$3e_i+2$ at greater heights. Such a prefix fixes its old word modulo
9. The literal ternary test therefore leaves the whole prefix or
empties it; the cofactor test gives one whole AP with the original
$m_i$ phase. There is no additional component mask. Owners outside
$U$ have protected complete subtrees and the same inverse conclusion.

Terminal outputs still have their fixed donors. For a continuing
output in the complete deletion hole, the total source stays in that
hole because it preserves modulo $9W$; original whole coverage then
supplies an owner whose entire inverse has just been enclosed. CD3,
the deep payments and all numerical-label freshness arguments apply
unchanged. No surjectivity of the total source is needed. Thus every
outcome again has an actual all-short triple. CD11 and CD12 hold with
these refined component indices and the corresponding actual profile
counts. The effect on the moment is still not monotone.

There is a stronger common-source inventory statement for either
component construction. **Every vertex belongs to a clique of at least
$n$ vertices, one at each moving first digit.** Start with its complete
private point and vary only the first q-digit. All new owners contain
the same preserved pair $(u,w)$, so they are pairwise adjacent. At the
initial digit the point is unchanged and its unique owner is the
initial vertex. The other digits give distinct actual labels. This
clique uses different first digits; it is not bounded by SNC1's
fixed-first-digit incidence cap.

### Verification scope and remaining inequality

A scoped transient Lean check confirms whole-support component
constancy on an arbitrary base set; six-subset inclusion counts and
their falling-factorial form; one common five-word/component-subset
experiment; the pointwise bad-group union bound; the six-profile
aggregation in CD12; and the opposite effects of C1 and C3 splitting
for $n>6$. The check compiles with only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. Its arbitrary base
includes both W and $\mathcal A\times W$ supports. It reuses the
pinned Mathlib finite-set, connected-component and counting results;
it introduces no retained mathematical declaration.

The complete arithmetic decoder, AP inverses, actual family-to-event
mapping, private-point inventory and EB1 payment contradiction above
are ordinary mathematical deductions, not a claim of end-to-end Lean
verification. In particular, the finite moment check takes the
pointwise existence of a bad group as a premise.

The divisor-controlled route CD8 still needs its own $D_h$ inventory,
actual phase and color distribution, and a contradictory upper bound.
The component route CD12 has $n\ge83$ under the additional GHA11
height envelope, but still needs an upper bound on its actual
component profiles contradicting CD12. Every surviving repeated-digit
and distinct-digit profile must be included. SC483 supplies neither
upper bound by itself. The
height-two branch and unrestricted odd distinct covering
remain unresolved.
