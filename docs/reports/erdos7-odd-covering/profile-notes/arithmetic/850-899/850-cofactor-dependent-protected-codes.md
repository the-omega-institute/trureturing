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

### Independently chosen words with protected complete subtrees

Under the additional inventory condition $78\le n\le111$, the
five-word choice need not be global. Fix the depth-three q-terminal
and depth-four 3q-terminal over different safe words. The 41 remaining
depth-four slots are distributed as $6,8,9,9,9$ among the five words.
Reserve six slots in each word. The other eleven slots yield 33 fixed
long leaves at depth five.

In each component, select six of the thirty reserved slots as short
leaves and expand the other 24 slots to long leaves. This gives

$$
6+3\cdot24=78
\tag{CD15}
$$

moving positions. Add $n-78$ of the 33 fixed long leaves to the moving
block. The remaining $111-n$ fixed long leaves accommodate every
protected continuing digit. Fix their entire dictionaries and both
terminal paths across all rows. In particular every unit-cofactor
owner remains protected. Different components may choose different
short-slot geometries, but each complete decoder remains fixed on its
owners' whole supports. The short 81-way and long 27-way continuations
both reach depth eight, so deep inverses retain depth $3e+2$ and the
same carrier $3^{3G+2}W$.

For a specific common experiment, independently choose one uniform
word $z_C\in\mathcal A$ in every component and use its six reserved
slots as the short leaves. Independently assign $U$ bijectively to that
component's moving positions. Its short digits are a uniform six-subset
of $U$, independent of $z_C$.

For a shallow triple whose three digits lie in $U$, let $T_{m,C}$ be
the intersection of the word demands of its owners in component $C$:
row zero demands $\mathcal A$, row one demands
$\mathcal A\cap[b_m]_3$, and row two demands $\{z_m\}\cap\mathcal A$.
An empty intersection gives probability zero. With $r_{m,C}$ defined
as in CD11, the exact probability is now

$$
\boxed{
p_m=\prod_{C:r_{m,C}>0}
\frac{|T_{m,C}|}{5}\frac{(6)_{r_{m,C}}}{(n)_{r_{m,C}}},
\qquad \sum_m p_m\ge1.
}
\tag{CD16}
$$

The product is one joint experiment, shared by all groups. If the
middle and top owners share a component, their root and word must be
compatible. In different components their word factor is
$|\mathcal A\cap[b_m]_3|/25$, including when the middle root disagrees
with $z_m$. Such triples cannot be removed using CD11's global
compatibility filter. A component containing only the bottom owner
has word factor one. The same full-source payment proves the pointwise
bad-group premise of CD16. No monotone change of its total moment is
asserted.

### Components inside the exact retained-family hole

A further refinement uses the full joint liability of
[Report385, PH1--PH2](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#1-replace-only-the-region-that-depends-on-the-changed-classes).
Delete all q-bearing originals and retain all q-free originals. Let
$E_0\subseteq\mathcal A\times\mathbb Z/W\mathbb Z$ be the exact set
missed by the retained family. Because $H_3=2$, all its tests factor
through these preserved coordinates. Its lift is the entire joint
deletion hole; it is fixed before any code or original owner is chosen.

Replace the full support $R_i$ by

$$
F_i=R_i\cap E_0
\tag{CD17}
$$

in the intersection graph, keeping every moving owner at every height.
Each $F_i$ is nonempty by original privacy. On $E_0$, choose the
decoder row by the component of these complete $F_i$ supports. Outside
$E_0$, use an arbitrary fixed row respecting the protected subtrees.
Every output still has one full source preserving modulo $9W$.

For an output in the lifted $E_0$, source membership in owner $i$
forces its preserved pair into $F_i$ and hence fixes the decoder to
$\theta_{\kappa_i}$. The **entire liability-restricted continuing
inverse** is therefore contained in one fixed-row AP with the original
$m_i$ phase. Let $B_i$ denote its assigned global AP enclosure, and
$H_{\rm ret}$ the complete retained union on the output carrier. The
whole raw continuing inverse $I_i$ satisfies

$$
I_i\subseteq H_{\rm ret}\cup B_i.
\tag{CD18}
$$

The raw inverse need not itself be an AP: it may split outside the
hole. Every such part is already paid by $H_{\rm ret}$. This is why
the exact common hole permits the refinement; an arbitrary favorable
mask or selected private subset would not justify CD18.

Apply CD3 to each group's nonempty restricted shallow inverses.
Empty restricted inverses cost no replacement. Every nonempty one
still receives one global enclosure, with the same label ranges and
strict grouped price comparison. Deep restricted inverses keep their
usual enclosures; the fixed terminal donors remain paid. Outside the
hole the retained family covers, and inside it the preserved source
and original whole coverage supply an enclosed owner. Thus absence
of a three-short restricted group gives the same complete EB1 descent.
No extra progression is charged for the shape of $E_0$.

For each shallow owner, define its actual word availability

$$
\mathcal A_i=\{u\in\mathcal A:\exists w,\ (u,w)\in F_i\}.
\tag{CD19}
$$

This is a fixed nonempty set. A selected short inverse is nonempty
exactly when its component's word belongs to $\mathcal A_i$: retained
tests do not depend on higher ternary digits, so any witnessing
cofactor point is compatible with the entire selected short prefix.
In particular the top owner's set is $\{z_m\}$, while the bottom and
middle owners may have fewer available words than their bare ternary
tests permit. Formula CD16 holds with

$$
T_{m,C}=\bigcap_{a:\kappa_{m,a}=C}\mathcal A_{m,a}.
\tag{CD20}
$$

All digit and word choices still belong to one joint law. The sets in
CD19 are determined by the original retained family, so they do not
introduce code-dependent conditioning of an unrelated cofactor law.

At every point $(u,w)\in E_0$, fix any higher q-suffix and vary the
first digit through $U$. Every resulting original source misses the
retained q-free family. Whole coverage supplies one moving owner at
each digit, and all their $F_i$ contain this same point. They form an
actual $n$-clique. Consequently the component unions partition all of
$E_0$, and every point in each component is supported at every moving
first digit. This statement uses the exact whole-cover hypothesis.

### One component contains a rectangular top inventory

The missing-cell argument of Report388, SC473--SC474 can now be
applied to independently chosen component codes. For a component $C$
and safe word $z$, define $D_C(z)\subseteq U$ to contain the digits
$c_2(m)$ of actual nonunit shallow triples whose three digits lie in
$U$, whose top owner belongs to $C$, and whose top word is $z$.
This is an actual inventory; no hypothetical simultaneous realization
of its different cofactors is assumed. Set

$$
S_C=\{c\in U:\forall z\in\mathcal A,\ c\in D_C(z)\}.
$$

Then, for the full-support or exact-hole component construction,

$$
\boxed{\exists C:\quad |S_C|\ge n-5.}
\tag{CD21}
$$

Suppose every component had at least six digits outside $S_C$. Choose
six such digits in each component and, for each chosen digit, one
missing word. Use the arbitrary-six-slot version of CD15 to place
each digit on a short leaf above its chosen word: at most six digits
request any word, and six reserved slots are available there. Expand
the other 24 reserved slots, complete the moving-block bijection and
keep all protected subtrees fixed. All components have thus been
assigned one simultaneous lawful source.

Any bad triple must have its top digit on one of those short leaves,
with the leaf's old word equal to its actual top word. Since every
digit outside $U$ is protected at a long leaf or a terminal, all three
digits of a bad triple lie in $U$. Its top owner would therefore
witness an occupied cell in the very $D_C(z)$ declared missing.
This is impossible. The complete paid replacement then contradicts
EB1, proving CD21.

Each of the $|S_C|$ digits in this one component has an actual top
owner at every one of the five safe words. Different digit/word cells
require distinct numerical labels $9qm$, since each original has
only one literal digit and word. Thus this **same component** contains
at least $5(n-5)$ distinct nonunit top originals, at least 390 when
the additional GHA11 envelope gives $n\ge83$. This is a rectangular
inventory, not a common-source clique of 390 labels. The owners of
different cells can have different cofactor phases and need not meet
one point. It supplies no contradiction to SNC1's pointwise cap.

### A resolution constraint for full-support components

This paragraph concerns the full $R_i$ intersection graph of CD13,
not the finer $F_i$ graph in CD17. Let $p\mid W$, and suppose
$h=p^{10}\mid W$. The retained-pure repair of Report385, RP1--RP4
bounds the number of original h-multiples in each actual h-phase by
24. Here is the exact consumer.

Retained pure 3 and 9 leave fifteen fresh ternary roots modulo 27
inside any h-phase. Use eleven fresh leaves at ternary height three,
eleven at height four, then three at height five. The first eleven
leave four roots, their twelve children leave one, and its three
children complete the repair. Assign all eleven divisors of $h$ to
each of the first two layers, and $1,p,p^2$ to the last. The 25
distinct new labels are $27p^b,81p^b$ for $0\le b\le10$ and
$243,243p,243p^2$. They are globally fresh because $H_3=2$.
Their sum satisfies, for $p\ge5$,

$$
108\sigma(p^{10})+243(1+p+p^2)
<351\sigma(p^{10})<\frac{1755}{4}p^{10}<625p^{10}.
\tag{CD22}
$$

Twenty-five distinct odd h-multiples have sum at least
$h(1+3+\cdots+49)=625h$. Deleting any 25 originals in one
h-phase and inserting the repair covers their entire union together
with the retained pure guards, at every lift. Count is unchanged and
sum decreases, contradicting EB1. The resulting phase cap 24 covers
all ternary rows, q-heights and first q-digits; it is not an extension
of SNC1.

Assume $n\ge25$ and let a moving bottom-row owner have modulus
$q^j p^k$. Then every moving owner whose full support meets its
coarser cylinder satisfies

$$
R_\ell\cap
\bigl(\mathcal A\times[\rho_i]_{p^{\min(k,9)}}\bigr)
\ne\varnothing
\quad\Longrightarrow\quad \kappa_\ell=\kappa_i.
\tag{CD23}
$$

For $k\le9$ this is direct intersection with $R_i$. Otherwise,
suppose the two components differ. The anchor has no ternary
restriction, so their full cofactor congruences must be incompatible.
Meeting its $p^9$ cylinder and CRT then force $p^{10}\mid m_\ell$
and $\rho_\ell\equiv\rho_i\pmod{p^9}$. In particular **every**
point of $R_\ell$ lies in that coarse cylinder. Choose any actual
private point of $\ell$ and its all-$U$ clique. Every clique owner
is in $\ell$'s component and disjoint from the anchor, so the same
CRT test forces $p^{10}$ into each cofactor. All $n$ owners share
the one actual $p^{10}$ phase of the chosen point, contradicting
the cap 24.

This selects no private point from an arbitrary intersection:
divisibility first forces the whole second support into the coarse
cylinder. A shallow prime-power triple whose three cofactor phases
agree through $p^{\min(k,9)}$ therefore has all three owners in one
full-support component. Separating its repeated digit only above the
ninth p-adic digit cannot suppress that triple's component probability.
The result does not truncate any original numerical modulus, give a
component-size upper bound, or extend automatically to masked supports.

There is also a multi-prime version on actual unpaid points. For a
moving bottom-row anchor $q^jm$, put

$$
g=\prod_{p\mid m}p^{\min(v_p(m),9)},\qquad
t_{10}(m)=\#\{p\mid m:v_p(m)\ge10\}.
$$

For full-support components,

$$
\boxed{
n>24t_{10}(m),\quad (u,w)\in E_0,\quad
w\equiv\rho_i\pmod g
\quad\Longrightarrow\quad (u,w)\in V_{\kappa_i}.
}
\tag{CD24}
$$

Indeed the actual unpaid point has an $n$-owner clique, all in one
full-support component. If that component differed from the anchor's,
each owner's full support would be disjoint from the anchor. Since
the anchor has no ternary restriction, CRT gives an incompatible
prime-power cofactor test. Agreement with $\rho_i$ through $g$ forces
the conflicting prime $p$ to have $v_p(m)\ge10$ and forces
$p^{10}$ to divide that owner's cofactor. For each such $p$, all
owners charged to it share the actual phase $w\bmod p^{10}$.
The cap 24 and a finite union bound give $n\le24t_{10}(m)$,
a contradiction.

Thus every owner whose full support meets
$E_0\cap(\mathcal A\times[\rho_i]_g)$ is in the anchor's component.
When $n\ge83$, CD24 applies whenever $t_{10}(m)\le3$, regardless
of the number of smaller exponents. This
does not choose a private point in a favorable intersection: whole
coverage is applied at the actual unpaid point itself. It asserts
nothing about points outside $E_0$. Nor does it extend to the masked
component graph, where separation may be caused by the retained cover
even when the full congruences are compatible.

### A common finite window for both component indices

There is a different, two-actual-point argument which also applies
to the masked graph. Select a finite set $S$ of cofactor primes and
put

$$
W_S=\frac{W}{\prod_{p\in S}p^{(v_p(W)-9)_+}}.
\tag{CD25}
$$

Assume $n>24|S|$. Every nonempty actual coarse fiber

$$
\mathscr F_{u,v}=\{(u,w)\in E_0:w\equiv v\pmod{W_S}\}
$$

is contained in the masked supports of at least $n-24|S|$ actual
moving owners, with distinct first q-digits and with cofactors dividing
$W_S$.

Choose one actual point in this fiber and its $n$-owner clique. For
each selected $p$, at most 24 of these original labels can have
$p^{10}$ in their cofactor: they share the chosen point's literal
$p^{10}$ phase. A union bound leaves at least $n-24|S|$ owners with
no selected $p^{10}$. Each such cofactor $m_\ell$ divides $W_S$,
because $m_\ell\mid W$, the unselected exponents are unchanged, and
every selected exponent of $m_\ell$ is at most nine. Its literal
cofactor test therefore holds at **every** point of the same coarse
fiber; the old word $u$ is also unchanged. All these points are
actually in $E_0$, so the whole fiber lies in $F_\ell$.

In particular the pointwise masked-component index, as well as the
full-support index, satisfies

$$
\boxed{
(u,w),(u,w')\in E_0,\quad w\equiv w'\pmod{W_S}
\quad\Longrightarrow\quad
\kappa(u,w)=\kappa(u,w').
}
\tag{CD26}
$$

For $n\ge83$ and $|S|\le3$, at least eleven actual owners contain
the entire fine fiber. The common vertices are chosen at one actual
point and work simultaneously everywhere on that fiber. This does
not independently choose incompatible owners at its different points.

This proof does not transfer CD24's arbitrary full-support intersection
to a masked intersection. It forces a shared owner at the two actual
endpoints themselves. Consequently it needs no bottom-row anchor,
no intermediate uncovered path, and no assumption that the mask is
constant on the coarse fiber.

There is an equivalent graph statement. Project each $F_i$ by
$\pi_S(u,w)=(u,w\bmod W_S)$ and join owners whose projected supports
intersect. The projected graph has exactly the same connected
components as the original masked graph. Indeed an original edge
projects to an edge. For a new projected edge $i,j$, choose its two
actual witnesses in one coarse fiber. A common owner $\ell$ supplied
above meets $F_i$ at the first witness and $F_j$ at the second, giving
an original path of length at most two. Thus coarse projection creates
no new component merger. It can create new pairwise intersections;
equality of the original and projected intersection graphs is not claimed.

Under the additional GHA11 envelope, choose the full available digit
set $U=\mathbb F_{113}\setminus P$ and take
$S=\{5,7,11\}\cap\{p:p\mid W\}$. Then $G\le10$ gives
$n\ge83>72$, and the carrier for the component index has bounds

$$
v_5(W_S),v_7(W_S),v_{11}(W_S)\le9,
\qquad v_p(W_S)\le11\quad(p\ge13).
\tag{CD27}
$$

The second bound uses the actual GHA11 table
$H_p\le10+\lfloor23/(p-1)\rfloor$; it does not follow from the
prime-support bound alone. CD26 says that the component index descends
to the **image of $E_0$** in this finite window. It does not assert
that membership in $E_0$ itself, every individual owner support,
or all raw inverse APs descend. Computing the projected supports still
requires their actual joint realizability. The decoder continues to
preserve the full original modulo-$9W$ coordinate.

The masked component classes and the available-word sets used in CD16
and CD21 are unchanged by this graph projection. Their unknown
profile and moment upper bounds are therefore still required; the
finite window is not a whole-cover contradiction.

## A one-digit insertion concentrates compatibility at height two

Keep one globally count-then-sum-minimal finite distinct odd nonunit whole cover
with actual labels $d_i=3^{a_i}q^{j_i}m_i$, where $a_i\le2$, $q>27$,
$\gcd(3,q)=\gcd(W,3q)=1$, $W>0$, and $m_i\mid W$. Fix any finite bound
$G\ge2$ for all $j_i$. Suppose at least one actual original has
$j_i\ge2$. Retain every original with $j_i\le1$, and let $R$ be their
exact integer complement. Its membership depends only on

$$
s=(u,c,w)=(x\bmod9,x\bmod q,x\bmod W).
\tag{CD28}
$$

Every actual deep original has a complete private point in $R$.
For each source $s$ of $R$, let $\mathcal G(s)$ consist of second
q-digits that have no top-row original active at this same source,
at any higher q-depth. Whole original coverage then gives deep
low-row service on every complete tail above each digit in
$\mathcal G(s)$. This definition does not assume that the sets
$\mathcal G(s)$ contain any fixed common alphabet.

For each actual low-row height-two original $i$, assign one tag
$\sigma_i\bmod3^{a_i+3}$. The tag belongs to that original and cannot
vary with $w$. On nonnegative target integers, impose

$$
\begin{split}
\forall x\in R\cap\mathbb N\quad\exists b\in\mathcal G(s(x)):
\qquad\qquad\qquad\qquad\\
\forall i\ [a_i\le1,\ j_i=2,\ i\text{ matches }(s(x),b)]
\quad x\equiv\sigma_i\pmod{3^{a_i+3}}.
\end{split}
\tag{CD29}
$$

Matching uses the actual ternary phase, the full cofactor phase and
both initial q-digits. All tests in CD29 depend only on $s(x)$ and
$x\bmod81$. CD29 is an additional premise, not a consequence of a
count of good roots at separate sources. It is sufficient, not a
necessary characterization of every insertion decoder. It excludes
roots where a top owner overlaps a usable low-row owner, and requires
tag compatibility of every active short owner rather than only a
suitable actual payer. Failure of CD29 does not exclude those broader
choices.

### Complete source and inverse payment

Choose one such $b=h(x)$. For a nonnegative target $x\in R$, write
$x\equiv c+qt\pmod{q^{G-1}}$, and use CRT to define a source $T(x)$ by

$$
T(x)\equiv x\pmod{9W},\qquad
T(x)\equiv c+qh(x)+q^2t\pmod{q^G}.
\tag{CD30}
$$

The $G=2$ tail is empty. The source keeps the first q-digit and the
complete old modulo-$9W$ data, so it avoids every retained original.
Its selected second digit excludes every top original. Its actual
owner therefore has $a_i\le1$ and $j_i\ge2$.

For an owner with $j_i\ge3$, remove its second q-digit and retain
all later literal digits. If its q-prefix is
$c_i+qb_i+q^2t_i\pmod{q^{j_i}}$, assign it the AP with modulus

$$
d_i'=d_i/q=3^{a_i}q^{j_i-1}m_i
\tag{CD31}
$$

and phases $\rho_i\bmod3^{a_i}$, $c_i+qt_i\bmod q^{j_i-1}$ and
$\rho_i\bmod m_i$. Equation CD30 puts the entire inverse
$(R\cap\mathbb N)\cap T^{-1}(A_i)$ inside this AP. The test selecting $b_i$ may be
dropped from the enclosure. Consequently these higher owners need no
additional constancy of $h$ on their cofactor cylinders.

For an owner with $j_i=2$, assign the AP with modulus

$$
d_i'=3^{a_i+3}q m_i
\tag{CD32}
$$

and phases $\sigma_i\bmod3^{a_i+3}$, $c_i\bmod q$ and
$\rho_i\bmod m_i$. CD29 supplies the required ternary congruence
for every nonnegative point of its complete inverse. The same tag is used at all
of its cofactor sources.

Delete all originals with $j_i\ge2$, including their top rows. Emit
one AP for each deleted low-row original, even if its inverse is
empty. Retained originals cover the complement of $R$; every nonnegative
target in $R$ is covered by the enclosure of the actual owner of $T(x)$.
This first covers all nonnegative integers. Periodicity of the finite
AP family then gives a whole integer cover.

The numerical labels have three disjoint ranges. Retained originals
have q-height at most one and ternary height at most two. Outputs
from $j_i\ge3$ have q-height at least two and ternary height at most
one; division by the same $q$ is injective. Outputs from $j_i=2$
have q-height one and ternary height three or four, which recover
$a_i$ and then $m_i$. They are injective by original numerical
distinctness. All outputs are odd nonunits. A new label may equal
the number of a deleted original; that is harmless. Freshness is
required against retained labels, not against all old labels.

The new class count never increases, and decreases if a deep top
original was deleted. If it stays equal, at least one deep low-row
original is replaced and every replacement strictly decreases its
modulus:

$$
\frac{d_i'}{d_i}=
\begin{cases}
1/q,&j_i\ge3,\\
27/q,&j_i=2.
\end{cases}
\tag{CD33}
$$

Either outcome contradicts global minimality. This rules out a
simultaneous tag assignment satisfying CD29 under the stated
whole-cover hypotheses.

### What remains to force the tags

Only height-two low-row owners appear in CD29. Higher low-row owners
retain their literal tails through CD31, even when the chosen second
root varies with the complete cofactor source. This reduces the
synchronization problem but does not solve it.

For the additional $q=113$, $G\le10$, $\omega(W)\le27$ hypotheses of
Report385 SNC3, every source of $R$ has at least 76 good roots. This
counts availability before the tags are chosen. The same middle-row
owner can occur at three different modulo-9 words and receives only
one modulo-81 tag; a bottom-row owner can span both surviving
modulo-3 roots and receives one modulo-27 tag. Separate choices at
these sources need not respect that common commitment.

The global cap in Report385 SNC14 limits top owners at each fixed
$(u,c,b)$ to two, across all cofactor sources. GLC1 additionally
supplies a fixed exceptional set of at most two top owners for each
$(u,c)$. These are actual joint constraints to preserve in a tag
analysis; neither is replaced by a pointwise root count. No argument
here derives CD29 from them or concludes unrestricted noncoverage.

A cache-guarded exact application checks CD29 on nonnegative targets,
the inserted source, complete higher inverse enclosure, numerical
labels, whole integer reassembly and the minimality contradiction.
All fifteen axiom-closure reports use only `propext`, `Classical.choice`
and `Quot.sound`, with no errors or `sorryAx`. The final statement
chooses its finite height bound internally. It does not prove CD29
from the original-cover assumptions, and adds no canonical declaration
or freeze.

## A finite congruence-family control for shared tags

The top-owner cap, the fixed exceptional-set condition, private points
and the finite height envelope do not by themselves force CD29. The
following family satisfies those restrictions and has at least 97
projected good roots at every source, yet no shared tag assignment
satisfies CD29. It is not a whole cover and has no EB1 property.

Put $q=113$. Label the vertices of $K_{16}$ by the sixteen primes from
17 through 79, and label its first 113 lexicographically ordered edges
by $r=0,\ldots,112$. For each vertex prime $p$, number its incident
edges by $k=1,\ldots,\deg(p)$. For each $u\in\{0,3,6\}$ and each
incidence $(p,r)$, set

$$
n=(u/3)\deg(p)+k,\qquad
 e=1+(n-1)\bmod10,\qquad
 j=2+\lfloor(n-1)/10\rfloor.
$$

Include the top class of modulus $9q^jp^e$ with phases $u\bmod9$,
$qr\bmod q^j$ and $k\bmod p^e$. Include one middle class $B_r$ of
modulus $3q^2m_r$ for each root, with phases $0\bmod3$,
$qr\bmod q^2$ and $0\bmod m_r$. Here the $m_r$ are the first 113
lexicographically indexed distinct numbers $5^a7^b$ with
$0\le a,b\le10$ and $(a,b)\ne(0,0)$. Finally include $1\bmod3$ and
$2\bmod9$. Take $W$ to be the product of the tenth powers of these
18 cofactor primes.

There are 678 top classes, 113 middle classes and two retained classes.
The pair $(e,j)$ recovers $n$, so their 793 numerical labels are
pairwise distinct. All are odd nonunits, with ternary height at most
two, q-height at most six and cofactor-prime heights at most ten. These satisfy the numerical
height and prime-support envelope used with GHA11, without claiming
its whole-cover hypotheses. Each original has a private point. For a top
owner choose its own literal phases, set the 5- and 7-coordinates to
one and all other vertex coordinates to zero. For $B_r$ set every
cofactor coordinate to zero and the q-prefix to $qr$. The retained
classes have private points 1 and 2. Nevertheless 5 is uncovered.
Divisor closure also fails: the modulus $191535=3q^2\cdot5$ occurs,
but the modulus 5 does not.

At fixed $(u,c=0,r)$ there are exactly two top originals. At fixed
$(u,c=0)$, distinct incidences at the same prime have distinct
nonzero phases modulo that prime because $\deg(p)\le15<p$.
Thus the literal collision graph is edgeless: GLC1 holds with no
exceptional originals. Each vertex prime blocks at most one root at
any cofactor source, leaving at least $113-16=97$ projected good roots.
Other first-q colors have no top activity.

### Shared tags fail, while separate word tags need not fail

On the diagnostic sources with $u\in\{0,3,6\}$, $c=0$ and the
5- and 7-coordinates zero, every root has complete low service from
its own $B_r$. Each $B_r$ nevertheless receives only one tag modulo81
across all three values of $u$. There are 27 compatible tag slots.
Any assignment of 113 roots to those slots has a slot $z$ containing
at most four roots. Tags incompatible with $0\bmod3$ can only reduce
the total size of these bins.

Every set of at most four distinct simple-graph edges has an injective
choice of incident vertices. Indeed, Hall's condition could fail only
for a subfamily having at most three incident vertices; a simple graph
on zero, one, two or three vertices has at most zero, zero, one or
three edges, respectively. Assign distinct endpoint primes to the
roots in the small bin. Set each assigned prime coordinate to the
literal incidence phase $k$, and every unassigned vertex coordinate
to zero. CRT supplies a nonnegative target with these coordinates,
$x\equiv z\pmod{81}$ and $x\equiv0\pmod{q^5}$.

At this target, every root in the bin has an active top owner. Every
root outside the bin has its active middle owner with the wrong tag.
No root satisfies CD29. The extra zero q-tail also permits the selected
top owner and $B_r$ to meet the same complete inserted source; the
obstruction does not make that source lack a low payer.

Separate tags for each fixed $u$ have only nine slots. The same graph
contains nine pairwise edge-disjoint pools, each with five edges and
four incident vertices. A vertex can block at most one root, so each
pool retains a top-free root at every cofactor source. Assigning one
pool to each of the nine slots supplies these independent wordwise
root choices. They do not give one legal shared tag for each $B_r$.

### The remaining payable-owner condition

Allowing top/low overlap evades the shared-tag obstruction on the
diagnostic sources. Assign the $B_r$ tags surjectively onto the 27
compatible slots. For every such target, a root with the matching tag
has its actual low payer $B_r$ on every complete tail, whether or not
a top owner also meets the source. Its replacement of modulus
$81qm_r$ pays the target. This does not supply service on the whole
residual; the uncovered integer 5 remains.

For the original whole-cover problem, let $T_b(x)$ be CD30 with a
specified second digit $b$. The less restrictive sufficient obligation
is to find one fixed tag per short low owner such that

$$
\forall x\in R\cap\mathbb N\quad\exists b\quad\exists i:
\quad a_i\le1,\quad j_i\ge2,\quad T_b(x)\in A_i,\quad
\bigl(j_i=2\Longrightarrow
x\equiv\sigma_i\pmod{3^{a_i+3}}\bigr).
\tag{CD34}
$$

The root and the payable owner may depend on the complete target.
Top owners may overlap this source, and other active short owners
need not have compatible tags. The selected inverse of each payer,
rather than every source incidence of that original, must enter its
single replacement AP. CD31 still encloses every selected higher
inverse. The fixed tags supply CD32 for the selected height-two
inverses. Proving this existential service on the entire residual,
with the original family and its actual joint constraints, remains
unresolved. Neither the failure of CD29 nor the nine wordwise pools
settles it.

A second cache-guarded exact application checks CD34 with the explicit
CRT source and the internally chosen bound $G=\max(2,\max_i j_i)$.
It derives the existential paid coverage used by the same replacement
family and verifies the whole integer-cover contradiction. Its fifteen
axiom-closure reports are standard, with no errors or `sorryAx`.
This check assumes CD34; it neither derives it from whole coverage nor
adds top exclusion or compatibility tests for other owners.

[The exact-integer control program](../../../frontier/cover-geometry/second-insertion-tag-control/second_insertion_tag_control.py)
and [its reproducible results](../../../frontier/cover-geometry/second-insertion-tag-control/second_insertion_tag_control.json)
retain the concrete family and witnesses. The program rejects Python
optimization mode rather than silently skipping its assertions.

The finite graph core has a transient Lean check: the universal
113-to-27 pigeonhole and endpoint-selection statement, the exact first
113 edges of $K_{16}$, and the nine disjoint five-edge/four-vertex pools
compile with six standard axiom-closure reports and no errors or
`sorryAx`. The separate exact-integer program verifies all 793 labels
and private points, the stated caps, concrete targets defeating CD29,
and 27 actual top/low overlaps with successful replacement payment.
Its supplied-tag tests are not an exhaustive search over tag vectors
or cofactor sources. The arbitrary-tag conclusion uses the preceding
pigeonhole, Hall and CRT argument. The Lean graph check does not
formalize the 793-class arithmetic construction or claim a whole
cover, EB1, or unrestricted noncoverage.

## Q-free short outputs and transport of every higher original

A broader replacement uses the literal second-digit deletion for every
original with $j_i\ge3$, including the top row. For height-two low
originals, the output need not retain the first q-digit. Keep the same
finite globally count-then-sum-minimal distinct odd nonunit whole cover,
$a_i\le2$, positive $W$, $m_i\mid W$ and
$\gcd(3,q)=\gcd(W,3q)=1$. For this replacement assume $q^2>27$ and
at least one actual deep original. No upper bound on the q-heights is
imposed.

Retain exactly the originals with $j_i\le1$. For every $j_i\ge3$, let
$H_i$ be the AP with the original ternary and cofactor phases, the
q-prefix obtained by deleting the second q-digit, and modulus
$d_i/q$. Define

$$
U_*=(R\cap\mathbb N)\setminus\bigcup_{j_i\ge3}H_i.
\tag{CD35}
$$

For each height-two low original, choose one fixed tag and the q-free
output

$$
P_i(\sigma_i)=\left\{x\in\mathbb N:
 x\equiv\sigma_i\pmod{3^{a_i+3}},\quad
 x\equiv\rho_i\pmod{m_i}\right\},
\qquad a_i\le1,\quad j_i=2.
\tag{CD36}
$$

Its modulus is $3^{a_i+3}m_i$. The remaining sufficient condition is

$$
U_*\subseteq\bigcup_{a_i\le1,\ j_i=2}P_i(\sigma_i).
\tag{CD37}
$$

There is no old first-q or old ternary-phase test in CD36. The tags are
arbitrary fixed residues, and this is direct coverage by replacement
APs. A short original providing such an output need not own the earlier
inserted source $T_b(x)$. That source-ownership claim is not used.

### Legality and complete payment

Emit one output for every $j_i\ge3$ original and every height-two low
original. Only the height-two top originals have no output. The high
outputs have q-height at least two and ternary height at most two;
the retained labels have q-height at most one. Coprimality separates
these two groups, and division by the same q preserves distinctness
within the high group. The short outputs have ternary height three or
four, which determines $a_i$ and then $m_i$. These identify their old
numerical labels $3^{a_i}q^2m_i$, so short outputs are distinct and
fresh against both other groups. They are odd nonunits.

CD35--37 cover the complete nonnegative deletion residual. The
retained originals cover the complement of $R$, and finite periodicity gives
coverage of all integers. The class count decreases if a height-two
top original is deleted. Otherwise it stays equal, and every changed
label is cheaper:

$$
\frac{d_i'}{d_i}=
\begin{cases}
1/q,&j_i\ge3,\\
27/q^2,&j_i=2,\ a_i\le1.
\end{cases}
\tag{CD38}
$$

An actual deep original supplies either a deleted class or a strict
price decrease. Thus CD37 contradicts global minimality. In particular
$U_*$ is nonempty. This conclusion does not require pure originals of
modulus 3 or 9, a cofactor-prime cap, or a bound on the original
q-heights.

### Actual short supply without a height cap

Now additionally suppose q is prime, $q\ge5$, and write
$\omega(W)$ for the number of its distinct prime factors. At an
$x\in U_*$, consider all q inserted sources, with the old modulo-$9W$
data and first q-digit preserved. An actual owner cannot have
$j_i\le1$, since then x would be covered by a retained original. It
cannot have $j_i\ge3$, since its literal stripped AP would contain x,
contradicting CD35. Every source owner therefore has height exactly two.

At this same old modulo-9 word, first q-digit and complete cofactor
source, the existing prime-degree and matching restrictions bound
nonunit top owners by $\omega(W)+1$. Height-two unit top owners have
only one possible numerical label, $9q^2$, so there is at most one.
Consequently at least $q-\omega(W)-2$ second digits have an actual
height-two low payer. Different second digits require different actual
originals. Let $J(x)$ contain all height-two low originals matching
only x's cofactor phase. It includes the actual same-source payers,
so

$$
|J(x)|+\omega(W)+2\ge q
\qquad(x\in U_*).
\tag{CD39}
$$

Neither an old ternary-phase test nor a first- or second-q-digit test
belongs to the pooled set $J(x)$. The argument uses each actual
owner at its own inserted source; it does not aggregate choices from
different cofactor sources. At $q=113$ and $\omega(W)\le27$, CD39
gives at least 84 actual short low originals at every x in $U_*$,
without the earlier height-ten assumption.

### Reusing the balanced-incidence criterion on the pooled cofactors

Let $P$ be the actual projection of $U_*$ to $\mathbb Z/W$. Index
columns by all original height-two low labels, and put an entry one
at row w precisely when $w\equiv\rho_i\pmod{m_i}$. This includes
short labels from every old ternary phase and first q-color. The
pooled set in CD39 is precisely the row at $w=x\bmod W$, so every
row has at least $q-\omega(W)-2$ entries.

If the actual originals 3 and 9 are present, their disjoint phases
leave exactly 45 safe residues modulo81. Under the additional
hypotheses that this pooled incidence matrix is balanced and
$q-\omega(W)-2\ge45$, the classical polychromatic theorem already
cited in Report385 Section142 supplies one of 45 colors to every
original column, with every row seeing every color. Associate the
colors with the safe residues modulo81. A middle original receives
that residue modulo81; a bottom original receives its reduction
modulo27. For any x in $U_*$, a column of color $x\bmod81$ supplies
CD36. Hence CD37 holds, contradicting minimality.

This is an application of the cited ordinary balanced-hypergraph
result, not a new coloring theorem or a Lean verification of that
external result. The bottom output is one modulo27 AP; extending
from its chosen modulo81 residue does not clone the original or
create extra output labels. The earlier mixed-depth boundary-stability
premise is not required for this sufficient condition.

Balancedness of this actual cofactor-incidence matrix has not been
proved. CD39 supplies a uniform multiplicity bound, not a common
coloring. A forbidden incidence cycle at selected rows does not by
itself give a legal replacement of the complete original APs. The
remaining task is to obtain a simultaneous allocation on the actual
projection P, using whole-cover and minimality constraints that a
local noncover control cannot supply.

A scoped transient Lean application verifies the replacement-label
legality, the direct complete-coverage contradiction under CD37,
nonemptiness of CD35, the generic cofactor-only supply bound CD39,
and its 84-owner specialization. Its fifty axiom-closure reports use
only `propext`, `Classical.choice` and `Quot.sound`, with no errors or
`sorryAx`. These are applications of existing finite-family, modular,
counting and minimality results; no new canonical Lean declaration,
freeze or coverage record is introduced. The balanced-hypergraph
coloring implication retains the external-result boundary stated
above.

## The preserved first q-digit supplies a second label coordinate

Keep one finite globally count-then-modulus-sum minimal distinct odd
nonunit whole cover, with actual labels
$d_i=3^{a_i}q^{j_i}m_i$, $a_i\le2$, positive $W$, $m_i\mid W$,
and $\gcd(3,q)=\gcd(W,3q)=1$. Suppose $q\ge81$.
The second-digit transport has a further available coordinate: the
first q-digit is preserved. It can distinguish numerical output labels
without demanding another ternary digit.

This gives the qualified height conclusion

$$
j_i\le1\qquad\text{for every actual original }i.
\tag{CD40}
$$

The conclusion excludes an actual deep q-original under these
hypotheses. It does not exclude height-one q-originals or establish
noncoverage of the whole ternary-height-two branch.

### One fixed source and three short output signatures

To prove CD40, assume an actual $g$ has $j_g\ge2$. Choose a finite
$G\ge2$ bounding all actual q-heights. For each nonnegative target x
put $b=x\bmod81$, so $b<q$, and choose the CRT source

$$
\begin{aligned}
T(x)&\equiv (x\bmod q)+qb+q^2\lfloor x/q\rfloor
       &&\pmod{q^G},\\
T(x)&\equiv x&&\pmod{9W}.
\end{aligned}
\tag{CD41}
$$

It preserves the original ternary and cofactor data and the first
q-digit. Its second q-digit is exactly $x\bmod81$.

Retain every original with $j_i\le1$. Transport every $j_i\ge3$
original by literal second-digit deletion to its CD35 progression
$H_i$, of modulus $d_i/q$. For a height-two original define
$r_i=\lfloor\rho_i/q\rfloor\bmod q$ and use the following single
CRT progression, retaining its actual cofactor phase in every row:

| Old row $a_i$ | New numerical modulus | Required output conditions |
| --- | --- | --- |
| $0$ | $27m_i$ | $x\equiv r_i\pmod{27}$ and $x\equiv\rho_i\pmod{m_i}$ |
| $1$ | $27qm_i$ | $x\equiv r_i\pmod{27}$, $x\equiv\rho_i\pmod q$, and $x\equiv\rho_i\pmod{m_i}$ |
| $2$ | $81m_i$ | $x\equiv r_i\pmod{81}$ and $x\equiv\rho_i\pmod{m_i}$ |

The three signatures, written as powers of 3 and q, are

$$
(3,0),\qquad(3,1),\qquad(4,0).
\tag{CD42}
$$

Emit one output for every height-two original, including those with
$r_i\ge81$. The latter need not have any selected source preimage;
their additional APs do not impede coverage, legality or strict cost
reduction. Thus the complete output uses exactly one class per original.

### Complete coverage without a tag-allocation hypothesis

Take any target x. Original whole coverage supplies an actual owner i
of the single source $T(x)$. If $j_i\le1$, preservation of the old
ternary data, cofactor and first q-digit puts x in that retained
original. If $j_i\ge3$, the literal stripped-prefix identity puts x
in $H_i$.

If $j_i=2$, actual source ownership forces
$r_i=x\bmod81$. It also supplies the original cofactor phase at x.
For row one, preservation of the first q-digit additionally supplies
$x\equiv\rho_i\pmod q$. Hence x satisfies the appropriate row of
the table. Every target is covered by this one fixed output family;
no independent polychromatic coloring, balancedness or separate
pointwise tag choice is assumed. Finite periodicity gives coverage
of all integers.

### Numerical legality and the strict comparison

The short outputs have ternary height three or four, whereas both
retained originals and higher stripped outputs have ternary height
at most two. Within the short family, CD42 and coprimality recover
the old row and cofactor, hence its old height-two numerical label.
The high outputs have q-height at least two, separating them from
retained q-heights at most one; multiplication by q recovers their
old labels. All output numerical moduli are therefore distinct,
odd and greater than one.

Every changed label is strictly smaller, with ratios

$$
\frac{d_i'}{d_i}=
\begin{cases}
1/q,&j_i\ge3,\\
27/q^2,&j_i=2,\ a_i=0,\\
9/q,&j_i=2,\ a_i=1,\\
9/q^2,&j_i=2,\ a_i=2.
\end{cases}
\tag{CD43}
$$

The assumed actual deep original g makes the total modulus sum
strictly smaller at the unchanged class count. This contradicts
global minimality and proves CD40. The comparison permits larger
ternary heights in the competing cover; minimality only inside the
original height-two class would not suffice.

In particular an original support prime $q\ge83$ has height at most
one in this setting. At $q=113$, the actual-deep premise used in
CD35--39 is excluded. The q-free short-output restriction in that
earlier construction was stronger than necessary: retaining the
first q-digit in the middle output supplies a legal way around its
remaining common-tag obligation.

The height-one case has no preserved first q-digit when that digit
itself is deleted. The construction above consequently does not
settle that case, does not remove the prime q from the original
support, and does not prove unrestricted Erdős #7.

A scoped transient Lean application verifies CD40--43, including
the actual single-source coverage, the three short signatures,
all new numerical collisions, oddness and nonunit conditions,
periodic extension to all integers, and the unchanged-count strict
sum comparison. Its fifteen axiom-closure reports use only
`propext`, `Classical.choice` and `Quot.sound`, with no errors or
`sorryAx`. The proof assumes neither a tag allocation nor a
candidate-count bound. It reuses finite CRT, modular identities,
factorization, finite sums and the stated minimality comparator;
no new canonical binding declaration, freeze or coverage record is
introduced.

## Actual pure guards reduce the second-digit alphabet to 45

Take an actual globally count-then-modulus-sum-minimal odd
distinct nonunit whole cover with factorization
$d_i=3^{a_i}q^{j_i}m_i$, $a_i\le2$, $m_i\mid W$, and the stated
conditions $W>0$, $\gcd(W,3q)=\gcd(3,q)=1$. Suppose in addition that
the original family contains actual moduli 3 and 9. Then

$$
q\ge45\quad\Longrightarrow\quad j_i\le1\text{ for every original }i.
\tag{CD44}
$$

No primality of q, bound on $\omega(W)$, bound on the other
q-heights, or independent tag-allocation premise is required.

Let the two actual guard residues be $r_3\bmod3$ and $r_9\bmod9$.
The modulus-nine class cannot be contained in the modulus-three
class: removing a contained original contradicts minimal class
count. Thus $r_9\not\equiv r_3\pmod3$. The uncovered guard residues
in the modulus-81 window form

$$
S=\{u\in\mathbb Z/81\mathbb Z:
 u\not\equiv r_3\pmod3,\ u\not\equiv r_9\pmod9\},
\qquad |S|=81-27-9=45.
\tag{CD45}
$$

Choose one fixed injection $c:S\hookrightarrow\{0,\ldots,q-1\}$.
For targets outside the two actual guards, replace $b=x\bmod81$
in CD41 by $b=c(x\bmod81)$. The CRT source still preserves
$x\bmod9W$ and the first q-digit. Targets inside either guard
are already covered by that retained original.

For each height-two original, let
$r_i=\lfloor\rho_i/q\rfloor\bmod q$. Assign a fixed decoded tag
$t_i=c^{-1}(r_i)$ when $r_i$ belongs to the image of c, choosing
any fixed default tag otherwise. Use the same three numerical
output labels as CD42, with $t_i$ in place of $r_i$ in the
ternary output conditions. A safe target's actual height-two
owner satisfies $r_i=c(x\bmod81)$, so injectivity gives

$$
x\equiv t_i\pmod{81}.
\tag{CD46}
$$

The first-q and cofactor conditions transfer exactly as in CD41.
All higher originals undergo the same literal second-digit
deletion, and all shallow originals are retained. Consequently
the one fixed output family covers every target. Every original
still has exactly one output, including owners with no selected
source preimage. Distinctness, oddness, nonunit status and the
strict price ratios are those of CD42--43; an actual deep
original would strictly decrease the total sum at unchanged
class count. This proves CD44.

For an original support prime $q\ge47$, the actual-guard version
therefore gives q-height at most one. It does not remove q from
the support or exclude a cover whose q-heights are all at most
one. The actual guard classes are hypotheses, not freely added
classes in the comparison cover.

A scoped transient Lean application verifies the entire CD44--46
chain, including actual guard separation, the 45-element safe
alphabet, its fixed injection and inverse tags, actual-source
payment, complete integer coverage and the unchanged-count
strict sum contradiction. All seventeen axiom-closure reports
use only `propext`, `Classical.choice` and `Quot.sound`, with no
errors or `sorryAx`. It reuses finite CRT, finite embeddings,
modular identities and minimality; it adds no canonical binding
declaration, freeze or coverage record.

## Two preserved q-digits bound the remaining depths

Take the same actual globally count-then-modulus-sum-minimal odd
distinct nonunit whole cover, with $d_i=3^{a_i}q^{j_i}m_i$,
$a_i\le2$, $m_i\mid W$, $W>0$ and
$\gcd(W,3q)=\gcd(3,q)=1$. There are two depth bounds:

$$
\begin{aligned}
q\ge27&\quad\Longrightarrow\quad j_i\le2\quad\text{for every }i,\\
q\ge15\text{ and actual original moduli }3,9
 &\quad\Longrightarrow\quad j_i\le2\quad\text{for every }i.
\end{aligned}
\tag{CD47}
$$

Neither assertion assumes primality of q or a prior upper bound on
the original q-heights. The guarded bound uses the actual two pure
classes in the original family.

Assume some actual $g$ has $j_g\ge3$. For the guarded assertion,
the safe residues modulo 27, outside those two disjoint guards,
number $27-9-3=15$. Choose one fixed injection of this safe set
into the q digits. At a safe target x denote its selected digit
by $b(x)$. Choose finite $G\ge3$ bounding every original q-height,
and use one CRT source

$$
\begin{aligned}
T(x)&\equiv (x\bmod q^2)+q^2b(x)+q^3\lfloor x/q^2\rfloor
 &&\pmod{q^G},\\
T(x)&\equiv x&&\pmod{9W}.
\end{aligned}
\tag{CD48}
$$

This preserves both first q-digits and inserts the selected third
digit. For the unguarded assertion use $b(x)=x\bmod27$ on every
target, which is a q digit when $q\ge27$.

Retain every original with $j_i\le2$. For every $j_i\ge4$, delete
the literal third digit of its q-prefix and use one progression
of modulus $d_i/q$. For $j_i=3$, assign a fixed tag $t_i$ modulo
27 by decoding its literal third digit through the selected
injection, with an arbitrary default outside the image. Its
single replacement is

$$
\begin{gathered}
d_i'=27q^{a_i}m_i,\\
x\equiv t_i\pmod{27},\qquad
x\equiv\rho_i\pmod{q^{a_i}},\qquad
x\equiv\rho_i\pmod{m_i}.
\end{gathered}
\tag{CD49}
$$

In the unguarded case $t_i$ is just the original third q-digit.
The three CRT moduli in CD49 are pairwise coprime. Actual ownership
of the single source forces its decoded tag; preservation modulo
$q^2$ supplies the q-prefix condition since $a_i\le2$. Hence every
safe target lies in its owner's retained or replacement class.
The actual guards cover unsafe targets. All originals contribute
one output, including those without any selected source preimage,
and finite periodicity extends the coverage to all integers.

The short labels have signatures $(v_3,v_q)=(3,0),(3,1),(3,2)$
when q is prime; the same coprime-power factorization distinguishes
the labels for composite q. The old row and cofactor are recovered
from each short label. Its ternary exponent three separates it
from every retained or higher stripped label. Higher stripped
labels have q-exponent at least three, whereas retained labels
have exponent at most two. Thus all output moduli are distinct
odd nonunits. Their strict price ratios are

$$
\frac{d_i'}{d_i}=
\begin{cases}
1/q,&j_i\ge4,\\
27/q^3,&j_i=3,\ a_i=0,\\
9/q^2,&j_i=3,\ a_i=1,\\
3/q,&j_i=3,\ a_i=2.
\end{cases}
\tag{CD50}
$$

They are less than one for $q>3$. The actual deep original g
forces strict sum decrease at unchanged class count, contradicting
global minimality and proving CD47.

Combining the guarded cases of CD44 and CD47 gives the following
restrictions on actual support primes in this same family:

$$
\begin{cases}
H_q\le2,&17\le q\le43,\\
H_q\le1,&q\ge47.
\end{cases}
\tag{CD51}
$$

The primes $5,7,11,13$ retain their previously established bounds.
These conclusions reduce the permissible exponent profiles; they
do not exclude all phases on the remaining profiles, or supply
the full squarefree-modulus hypothesis of the known squarefree
noncoverage theorem.

A scoped transient Lean application verifies both versions of CD47,
their single-source transport, safe-domain decoding, literal
third-digit deletion, legal short labels and the complete same-count
sum contradiction. All eighteen axiom-closure reports use only
`propext`, `Classical.choice` and `Quot.sound`, with no errors or
`sorryAx`. It reuses modular arithmetic, finite CRT, finite
embeddings, coprime-power decoding and the original minimality
comparator. It introduces no canonical binding declaration,
freeze or coverage record.

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

A second scoped transient check confirms the independent-word joint
experiment, arbitrary word masks $T_{m,C}$, its exact product
probability and the moment in CD16 under the explicit pointwise
bad-group premise. It also checks the 41/30/24/78/33 leaf counts and
the protected/moving partition for $78\le n\le111$. These checks use
only the same standard axioms. They do not impose the common-word
compatibility filter on different components.

A finite-selection check confirms the rectangular implication CD21:
the explicit obstruction for every componentwise six-subset and
per-digit word assignment forces one component with at least $n-5$
saturated digits. It checks the five-word rectangle cardinality, its
translation into distinct top labels when every cell has an actual
witness, and the bound 390 for $n\ge83$. The arithmetic construction
supplying that obstruction is an explicit premise of this check.

A separate transient check verifies CD22's divisor-sum and strict cost
chain, the 25-odd-multiple lower bound, the forest's scalar capacity,
and the CRT implication used in CD23, including that every point of
the second support lies in the coarse cylinder. It also checks the
25-versus-24 contradiction with explicit incidence and phase-cap
premises. The retained-pure arithmetic forest and EB1's implication
of the phase cap remain ordinary proof inputs.

The masked-source check verifies membership on $E_0$, the inclusion
of the entire raw continuing inverse in the retained complement plus
one fixed enclosure, and whole coverage after payment. The retained
complement is defined to be exactly the complement of lifted $E_0$.
It does not assume that a raw inverse is a single AP; arithmetic
fixed-prefix enclosure is an explicit premise. These checks use only
the standard axioms already listed.

A further transient check verifies the exact factorization of $W_S$,
its selected exponent formula, cofactor divisibility, and the common-owner
count for arbitrary finite $S$. With $|S|\le3$ and an actual clique of
at least 83 owners, it checks whole-fiber containment by at least eleven
owners and both component indices' factorization on the subtype $E_0$.
Literal incidence, the clique lower bound, and the phase cap of 24 are
explicit premises. All twelve checked axiom closures use only the
standard axioms listed above. The general $n>24|S|$ endpoint statement
and the projected graph's length-two-path corollary remain ordinary
deductions; neither was separately kernel-replayed.

The complete arithmetic decoder, AP inverses, actual family-to-event
mapping, private-point inventory and EB1 payment contradiction above
are ordinary mathematical deductions, not a claim of end-to-end Lean
verification. In particular, the finite moment check takes the
pointwise existence of a bad group as a premise. CD24's multi-prime
arithmetic translation and complete component conclusion have not been
kernel-replayed.

The divisor-controlled route CD8 still needs its own $D_h$ inventory,
actual phase and color distribution, and a contradictory upper bound.
The component routes have $n\ge83$ under the additional GHA11 height
envelope, enough for CD15. They still need an upper bound on the actual
profiles or word-availability moment contradicting CD12 or CD16.
Every surviving repeated-digit and distinct-digit profile must be
included. SC483 supplies none of these upper bounds by itself. The
height-two branch and unrestricted odd distinct covering
remain unresolved.
