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

## A remaining q-square forces an actual top-row label

Assume the same actual globally count-then-modulus-sum-minimal odd
distinct nonunit cover, $d_i=3^{a_i}q^{j_i}m_i$, $a_i\le2$,
$m_i\mid W$, $W>0$, $\gcd(W,3q)=\gcd(3,q)=1$, and actual original
moduli 3 and 9. A second-digit refinement gives

$$
q\ge15\ \text{and some }j_g\ge2
\quad\Longrightarrow\quad
\text{some actual }i\text{ has }a_i=2,\ j_i=2.
\tag{CD52}
$$

This assertion does not require CD47's height cap as a premise.

Suppose instead there is no such row-two, height-two original.
Use the 15 safe residues modulo 27, their one fixed injection into
q digits, and CD41's second-digit insertion. Its decoded tag need
only be known modulo 27: every height-two owner has row zero or
one, so its output is one of

$$
27m_i\quad\text{or}\quad27qm_i.
\tag{CD53}
$$

Their output conditions are those of CD44--46; the absent row-two
case requires no modulus-81 tag. Retain all $j_i\le1$ originals and
strip the second digit of every $j_i\ge3$ original. The same
single-source coverage, numerical distinctness, oddness and
nonunit proof applies. Every changed modulus strictly decreases
since $q>9$. An actual deep original makes the sum decrease at
the unchanged class count, contradicting global minimality and
proving CD52.

The established divisor-closure argument converts this actual
witness into the numerical-label conclusion

$$
q\ge15\ \text{and some }j_g\ge2
\quad\Longrightarrow\quad 9q^2\in D.
\tag{CD54}
$$

Indeed CD52 supplies an original modulus $9q^2m_i$. If its odd
nonunit divisor $9q^2$ were absent, replace only that original by
its containing congruence class modulo $9q^2$, keeping the original
phase reduced modulo this divisor. Every formerly covered integer
remains covered. The missing numerical label makes the new moduli
distinct; absence also makes the divisor proper, so the total
modulus sum strictly decreases at the same class count. This is
the existing minimal-divisor replacement, not a new assumption
that $m_i=1$.

For an actual support prime $17\le q\le43$, CD51 and CD54 give
$H_q\in\{1,2\}$, with $H_q=2$ forcing the actual numerical
modulus $9q^2$. The supplied label has its own original phase;
the argument prescribes no phase or cofactor source, and gives
no exclusion of all families satisfying these necessary conditions.

A scoped transient Lean application verifies CD52--54, including
the fixed safe-27 decoder, all higher original owners, complete
same-index replacement and the actual numerical divisor-closure
consumer. All nineteen axiom-closure reports use only `propext`,
`Classical.choice` and `Quot.sound`, with no errors or `sorryAx`.
The divisor step directly reuses the existing singleton repair
comparison and modular projection. No new canonical binding
declaration, freeze or coverage record is introduced.

## Every second-layer component needs many digits in each row

Keep the actual globally count-then-modulus-sum-minimal cover,
factorization, positivity, coprimality and actual pure 3 and 9
hypotheses of CD52, with $q\ge15$. Consider precisely the actual
height-two originals $J=\{i:j_i=2\}$. For $i\in J$, forget only
its second q-digit and retain its other literal conditions:

$$
B_i=\{x\in\mathbb N:
 x\equiv\rho_i\pmod{3^{a_i}},\quad
 x\equiv\rho_i\pmod q,\quad
 x\equiv\rho_i\pmod{m_i}\}.
\tag{CD55}
$$

Connect two height-two originals when these preserved supports
intersect. Connected components refer to this one fixed actual
family. An intersection here need not be an intersection of the
original progressions, whose second q-digits may differ.

For the component D of any $g\in J$ and each row $t\in\{0,1,2\}$,
form the distinct literal second q-digits of its members in that row:

$$
T_{D,t}=\{\lfloor\rho_i/q\rfloor\bmod q:i\in D,\ a_i=t\}.
\qquad |T_{D,t}|\ge q-14.
\tag{CD56}
$$

This counts distinct digits separately in each exact row. Fix t
and suppose the complement of $T_{D,t}$ has at least 15 digits.
Choose one fixed injection of the 15 safe residues modulo 27
into that complement. CD47 supplies $j_i\le2$ for every original.
Change only the originals in D, and put

$$
A=\bigcup_{i\in D}B_i.
\tag{CD57}
$$

At a target outside A, an owner from the original full cover
cannot belong to D, since each original in D is contained in
its preserved support. This owner is retained.

At a safe target in A, use the chosen safe-27 injection and the
second-digit CRT source from the CD52 proof. This source preserves
the target's first q-digit, ternary coordinate modulo 9 and
cofactor coordinate modulo W. If its actual owner has height at
most one, that retained original also covers the target. If its
owner i has height two, the target belongs to $B_i$. It already
belongs to some $B_d$ with $d\in D$, so this very target witnesses
an intersection, placing i in D. Its literal second digit equals
the selected code digit, which lies outside $T_{D,t}$. Hence this
actual owner cannot have row t. There are no higher owners by
CD47. Unsafe targets are covered by the retained actual guards.

Every selected changed owner therefore supplies one fixed decoded
tag modulo 27, its literal first q-digit, and its cofactor phase.
Assign new numerical labels as follows:

| Avoided row t | Output for row 0 | Output for row 1 | Output for row 2 |
|---|---:|---:|---:|
| 0 | $81m_i$ | $27m_i$ | $27qm_i$ |
| 1 | $27m_i$ | $81m_i$ | $27qm_i$ |
| 2 | $27m_i$ | $27qm_i$ | $81m_i$ |

The two active rows use the tag modulo 27 and the original
cofactor phase; the row assigned $27qm_i$ also keeps the first
q-digit. Emit an $81m_i$ output for every member of the avoided
row, with any fixed residue. Those owners have no selected source preimage, so their extra
outputs do not remove coverage. Each member of D contributes
exactly one output; every other original is retained.

For each fixed t the three new signatures are a permutation of
$(3,0),(3,1),(4,0)$ in ternary and q depth. They recover the old
row and cofactor, so the outputs are distinct odd nonunits and
fresh against every original outside D. The respective price
ratios in the table are

- $t=0$: $81/q^2$, $9/q^2$, $3/q$;
- $t=1$: $27/q^2$, $27/q^2$, $3/q$;
- $t=2$: $27/q^2$, $9/q$, $9/q^2$.

All are strictly below one for $q>9$. The nonempty component
therefore permits a same-count strict sum decrease, contradicting
global minimality. This comparator may have ternary heights three
and four; minimality restricted to $H_3\le2$ would not suffice.
The digit complement has at most 14 elements, proving CD56.

The construction neither assumes a common point in all the
supports of a component nor assembles independent source choices:
each coverage test uses one actual target and its one CRT source.

Since $q\ge15$, each component has a member in each exact row.
Every intersection preserves the literal first q-digit, yielding

$$
\forall g\in J\ \forall t\in\{0,1,2\}\ \exists i\in J:\quad
 a_i=t,\qquad i\in D_g,\qquad \rho_i\equiv\rho_g\pmod q.
\tag{CD58}
$$

At $q=37$, each component requires at least 23 distinct second
digits in each row; at $q=17$ it requires at least three per row.
These assertions do not place any particular numerical pure
$q^2$, $3q^2$ or $9q^2$ original in every component, align their
phases, or make the different digit witnesses simultaneously
active at one base point. No contradictory upper bound on the
actual component digit sets has been established.

A scoped transient Lean application verifies CD55--58, including
the actual rooted components, exact-row digit images, complementary
code pool, fixed decoder, row-permuted legal labels, complete
same-count replacement and the internally derived height cap.
All thirty-three axiom-closure reports use only `propext`,
`Classical.choice` and `Quot.sound`, with no errors or `sorryAx`.
The application reuses finite CRT, coprime decoding, finite
images and complements, equivalence closure and the existing
minimality comparison. No canonical binding declaration, freeze
or coverage record is introduced.

## An actual pure q-square reduces the second-digit threshold to 43

Under the actual globally count-then-modulus-sum-minimal odd-cover
hypotheses of CD52, with actual moduli 3 and 9, the necessary
height restriction strengthens to

$$
q\ge43\quad\Longrightarrow\quad j_i\le1\quad\text{for every original }i.
\tag{CD59}
$$

Suppose there is an actual $j_g\ge2$. CD47 first gives
$j_i\le2$ for every original. The existing numerical divisor
replacement supplies an actual pure $q^2$ original h. Coprimality
in the original factorization forces $a_h=0$, $j_h=2$, $m_h=1$.
Write its literal first and second q-digits as c and b. No phase
of another pure original is identified with h.

Delete exactly the originals with $j_i=2$ and first q-digit c.
The retained actual 3 and 9 classes leave 15 safe residues modulo
27 and 45 modulo 81. Choose one safe residue z modulo 27. Its
three lifts modulo 81 are safe. Encode all three by the single
q-digit b; encode the other 42 safe residues injectively into
q-digits different from b. The required alphabet has size

$$
45-3+1=43.
\tag{CD60}
$$

On the 45 safe residues, the compressed code has one three-element
fiber, all within a single residue modulo 27; every other nonempty
fiber consists of one residue modulo 81. This reuses the terminal pure-class
coding principle of Report388 SC461--465, with the preserved
first-q output signatures of CD42.

For a safe target with first digit c, form the same second-digit
CRT source, preserving its first q-digit and its coordinates
modulo 9W. On the compressed fiber the source belongs to the
actual pure $q^2$ class h, so explicitly select h. Its new
modulus is 27, and its fixed residue z covers all three target
lifts. No modulus-81 distinction is required for this selected
owner.

On every other code fiber, its q-digit uniquely determines the
target modulo 81. Any actual source owner of height at most one
is retained and also covers the target. A height-two owner has
first digit c and therefore belongs to the deleted set. Its one
fixed decoded residue provides the CD42 output: $27m_i$ in row
zero, $27qm_i$ in row one, and $81m_i$ in row two, keeping the
literal cofactor phase and, for the middle row, the first q-digit.
Unused outputs may have arbitrary fixed residues.

Outside first digit c, a target's original owner cannot be one
of the deleted originals. Unsafe targets are covered by the
retained actual guards. Every target is consequently covered by
the retained family and these outputs. Emit one output for every
deleted original, including h, even if a code digit is unused.
The established numerical signatures make the new moduli distinct
odd nonunits and fresh against the retained originals. Their
ratios to the old moduli are $27/q^2$, $9/q$ and $9/q^2$, all
strictly below one. The deleted set contains h, so the unchanged
class count has a strictly smaller modulus sum, contradicting
global minimality and proving CD59.

In the prime profile, CD59 makes every support prime at least
43 have height one. Together with CD47, primes 17 through 41
have height at most two. These remain restrictions on the same
hypothetical globally minimal cover, with actual 3 and 9 and
ternary height at most two; they do not exclude that entire branch
or prove unrestricted odd noncoverage.

A scoped transient Lean application verifies CD59--60, including
the actual numerical divisor and coordinate bridge, compressed
finite code, fixed owner tags, full original-family coverage and
the same-count strict sum contradiction. All twenty-nine
axiom-closure reports use only `propext`, `Classical.choice` and
`Quot.sound`, with no errors or `sorryAx`. The application reuses
the existing minimality comparison, finite embeddings, coprime
decoding and CRT; it introduces no canonical binding declaration,
freeze or coverage record.

## The actual private ternary projection controls the second-digit alphabet

Keep the actual globally count-then-modulus-sum-minimal family,
ternary heights at most two, actual moduli 3 and 9, and the coprime
factorization of CD52. In this section q is prime and $q\ge15$.
Suppose an original has q-height at least two. CD47 bounds every
q-height by two, and numerical divisor closure supplies an actual
pure $q^2$ original h. Use its complete original private region

$$
P_h=\{y\in\mathbb N:y\equiv\rho_h\pmod{q^2},\quad
 y\not\equiv\rho_i\pmod{d_i}\text{ for every }i\ne h\},
\qquad
\Lambda_h=\{y\bmod9:y\in P_h\},\qquad s_h=|\Lambda_h|.
\tag{CD61}
$$

Count minimality makes $P_h$ nonempty. Every point in it avoids
the actual 3 and 9 guards, whose phases are incompatible modulo
3. Consequently $1\le s_h\le5$. The necessary alphabet condition is

$$
\boxed{q<9s_h-2.}
\tag{CD62}
$$

This concerns the literal private region of that same original
h. It does not select a different cover or a separate favorable
cofactor point for each step of a replacement.

Write c for h's first q-digit, and delete precisely the originals
with q-height two and first digit c. Let E be the complete hole
left by the retained family. The existing prime-prefix liability
theorem, with parent depth one and preserved carrier 9W, gives

$$
x\in E\quad\Longleftrightarrow\quad
 x\equiv\rho_h\pmod q\quad\text{and}\quad
 \exists y\in P_h:\ y\equiv x\pmod{9W}.
\tag{CD63}
$$

Its noncontainment hypothesis is supplied by original count
minimality. In particular, a target in E has its residue modulo
9 in $\Lambda_h$. Preserving its entire coordinate modulo 9W
and its first q-digit keeps the source in E. The set
$\Lambda_h\times\mathbb Z/W\mathbb Z$ is only an envelope for
these source coordinates; no rectangularity of E is asserted.

Suppose $9s_h-2\le q$. There are $3s_h$ residues modulo 27 and
$9s_h$ residues modulo 81 above $\Lambda_h$. Choose one of the
former. Map its three lifts modulo 81 to h's literal second
q-digit, and inject the other $9s_h-3$ fine words into the other
$q-1$ digits. The alphabet therefore has exactly

$$
9s_h-3+1=9s_h-2
\tag{CD64}
$$

slots. Define this code on the entire projection envelope, so an
original's decoded enclosure is not further cut by an unknown
cofactor mask.

For a target in E, use the CRT source that preserves 9W and the
first q-digit and inserts the chosen second digit. On the collapsed
leaf, the donor's new modulus 27 directly covers the target. On
any other code fiber, the second digit determines one residue
modulo 81. The source remains in the exact hole by CD63, so its
actual owner belongs to the deleted family. The fixed decoder
then gives the same row labels $27m_i$, $27qm_i$, $81m_i$ as in
CD59. Outside E, an actual retained class covers the target.

Emit one output for every deleted original, including empty
inverses. The unchanged numerical-signature proof gives distinct
odd nonunit moduli, fresh against retained labels. Their respective
ratios $27/q^2$, $9/q$, $9/q^2$ are strictly below one. The donor
makes the deleted set nonempty; the same class count therefore
has smaller total modulus, contradicting global minimality. This
proves CD62 with the whole common-source liability retained.

CD62 requires at least three private words for every squared
prime above 13. The two-output construction in CD65--68 gives
the stronger projection requirements and prime-height cutoff.
Neither a projection cardinality nor its equality with the five
guard-safe words provides one cofactor coordinate common to
those words.

A scoped transient Lean application verifies CD61--64, including
the canonical prime-prefix liability specialization, actual private
projection, finite alphabet, same-source CRT transport, fixed owner
tags, unchanged class count and strict sum comparison. The actual
height cap is derived within the final application, and its
scalar consequences are checked in the same compilation. All
thirty-two axiom-closure reports use only `propext`,
`Classical.choice` and `Quot.sound`, with no errors or `sorryAx`.
The application adds no canonical binding declaration, freeze or
coverage record.

## A second actual deleted class supplies a second short output

Keep the prime-q and actual-family hypotheses of CD61. The
private-projection constraint strengthens to

$$
\boxed{q<9s_h-4,\qquad 1\le s_h\le5.}
\tag{CD65}
$$

The second saving uses an actual deleted class whose new output
can discard its cofactor. It does not require an aligned pure
$3q^2$ donor, a common cofactor point across private words, or an
empty top-row cell.

Let h be the actual pure $q^2$ original, c its first q-digit,
and D the height-two originals with first digit c. There is an
original in $D\setminus\{h\}$. Indeed, start with an actual
private point of h and replace only its second q-digit by a
different digit, preserving 9W and its first digit. The exact
hole identity CD63 keeps the new point in E. Its actual covering
owner belongs to D and cannot be h.

Choose $h_1\in D\setminus\{h\}$, giving priority to the original
of numerical modulus $3q^2$ if that original belongs to D.
Numerical distinctness makes this preferred original unique.
Let b and $b_1$ be the actual second digits of h and $h_1$.
They are different: otherwise the entire original class of
$h_1$ would be contained in h, contradicting count minimality.
These are all statements about the same original family.

Replace the normal output for $h_1$ by modulus $27q$. For every
other member of D use the established row labels. The complete
assignment is

$$
M_i=
\begin{cases}
27q,&i=h_1,\\
27m_i,&i\ne h_1,\ a_i=0,\\
27qm_i,&i\ne h_1,\ a_i=1,\\
81m_i,&i\ne h_1,\ a_i=2.
\end{cases}
\tag{CD66}
$$

The only normal output that could equal $27q$ is the row-one
unit-cofactor output, belonging to the actual numerical $3q^2$.
The priority rule selects it whenever it is in D, so this slot
cannot collide with another output. Coprimality separates it
from the other two row signatures. Every new label has ternary
height at least three, making it fresh against all retained
originals. The ordinary outputs remain pairwise distinct.

The selected $h_1$ is a proper numerical multiple of $q^2$,
so its old modulus is at least $2q^2>27q$ for $q\ge15$.
Thus its modified output is strictly cheaper even when its
original row is zero or two. All other outputs keep their
previous strict savings. The new family has one output for
each deleted original.

Suppose $9s_h-4\le q$. There are $3s_h\ge3$ residues modulo
27 above $\Lambda_h$, so select two distinct ones, $z,z_1$.
Map the three modulo-81 lifts of z to b, and the three lifts
of $z_1$ to $b_1$. Inject the other $9s_h-6$ fine words into
the remaining $q-2$ digits. The total alphabet is

$$
9s_h-6+2=9s_h-4.
\tag{CD67}
$$

Pay the first short leaf directly by h's new modulus 27 and
residue z. Pay the second directly by the new modulus $27q$,
with residue $z_1$ modulo 27 and c modulo q. This second output
covers the whole cofactor fiber. Its residue need not preserve
$h_1$'s former ternary or cofactor phase: the new arithmetic
progression pays the entire selected target leaf directly.

On any other code fiber the inserted digit is neither b nor
$b_1$. The actual CRT source, preserving the target's full 9W
coordinate and first q-digit, remains in the exact hole E.
Its original owner belongs to D and is neither h nor $h_1$.
The unique modulo-81 decoder and the original cofactor phase
supply that owner's ordinary CD66 output. In particular,
$h_1$ has no continuing inverse left unpaid. Retained originals
cover outside E. This gives a whole cover with the same number
of distinct odd nonunit moduli and a strictly smaller sum,
proving CD65.

Consequently the same actual-family assumptions give

$$
\boxed{q\ge41\quad\Longrightarrow\quad j_i\le1
       \text{ for every original }i.}
\tag{CD68}
$$

For an actual squared prime above 13, the remaining necessary
private-projection values are

| Actual squared prime q | Required private residues modulo 9 |
| ---: | ---: |
| 17, 19 | $s_h\ge3$ |
| 23, 29, 31 | $s_h\ge4$ |
| 37 | $s_h=5$ |

Thus the second output also strengthens the bound at 23.
The five words at 37 may still have different cofactor witnesses.
No exclusion of all squared primes, of the whole ternary-height-two
branch, or of unrestricted odd distinct covering follows here.

A scoped transient Lean application verifies CD65--68, including
the second original's existence and priority choice, two short
code fibers, full actual-hole transport, modified numerical
labels, whole-family coverage and same-count strict sum descent.
The final application derives the height cap and, for CD68, the
actual pure-square donor; neither a second donor nor a coding
pool is an extra hypothesis. Its three scalar table checks also
pass. All thirty-nine axiom-closure reports use only `propext`,
`Classical.choice` and `Quot.sound`, with no errors or `sorryAx`.
This reuses the existing source and comparison interfaces and
introduces no canonical binding declaration, freeze or coverage
record.

## A remaining square at 37 forces repeated-digit cofactor triples

Assume the same actual globally count-then-modulus-sum-minimal
odd distinct nonunit whole cover, actual pure moduli 3 and 9,
ternary heights at most two, and the common coprime factorization
used in CD65--68. Set q=37 and suppose an actual original has
q-height at least two. Numerical divisor closure supplies the
actual pure-square original h. Its complete private projection
Λ modulo 9 has five words by CD65.

Call an actual cofactor m a repeated-digit triple at (b,u) if the
three original labels

$$
q^2m,\quad3q^2m,\quad9q^2m
\tag{CD69}
$$
all have first q-digit c of h and second q-digit b, the middle
original accepts u modulo 3, and the top original has word u
modulo 9. The cofactor residues of the three originals remain
their actual separate residues. This definition makes no assertion
that those three cofactor sections have a common point, or that
each meets a prescribed fiber of the complete deletion hole.

The actual family must have a set T of at least 29 distinct second
digits, different from h's digit, such that

$$
\boxed{\forall b\in T\;\forall u\in\Lambda,\quad
\text{an actual nonunit repeated-digit cofactor triple exists at }(b,u).}
\tag{CD70}
$$

Consequently at least 145 distinct nonunit numerical cofactors
occur in these triples. This is a necessary restriction on a
remaining cover; it does not exclude q=37.

### Six available cells would give a complete exchange

Choose the actual second terminal h1 with the priority in CD65:
if the actual pure 3q² original lies in the deleted first-color
family D, take it as h1. Let b0 and b1 be the distinct second
digits of h and h1. If the actual pure 9q² original belongs to
D, denote its second digit by γ; otherwise choose any γ. Exclude
b0, b1 and γ, leaving at least 34 candidate digits.

A candidate digit is free if some word u in Λ has no repeated-digit
triple at (b,u). Suppose six candidate digits are free, and fix
one such word for each. At a chosen cell (b,u), SNC14 gives at
most two actual top originals. Each top original fixes its
numerical cofactor and hence its unique possible bottom and
middle counterparts. Since the cell is free, at least one of
those lower counterparts must use a different digit if the three
are to fit two selected cells. That other digit is unique.

Thus each chosen digit has at most two possible conflicting
partners. Six vertices have at most twelve directed conflicts,
whereas there are fifteen unordered pairs. Choose a pair with
no conflict in either direction. Write its digits as b2,b3 and
its selected words as u2,u3. No cofactor can then have all three
rows simultaneously compatible with these two selected cells:
a top owner in either cell would give the excluded conflict,
or a repeated-digit triple at that free cell.

Choose four distinct leaves modulo 27 above Λ. Two leaves have
parents u2,u3; these leaves can be distinct even when u2=u3.
Use the other two as the b0,b1 terminals. Collapse each leaf's
three modulo-81 lifts to its assigned digit and keep all other
fine words distinct. The required alphabet size is

$$
4+(45-12)=37.
\tag{CD71}
$$

Retain the exact same CRT source: preserve the entire old 9W
coordinate and first q-digit, and replace only the second
digit by this fixed code. The canonical complete-hole identity
keeps every source inside the complete deletion hole. It does
not replace that hole by a product of its projections.

Pay the b0 and b1 leaves directly with pure 27 and 27q.
For each nonunit cofactor m, allocate the remaining originals
in its group among

$$
27m,\quad27qm,\quad81m.
\tag{CD72}
$$

At most two inverses need a whole modulo-27 leaf, because
three would give the excluded triple. Assign them the first two
labels, and assign a fine or empty inverse to 81m. Equivalently,
choose a row with no potentially short inverse and swap that
row with slot two. This preserves injectivity within each group.
If h1 has nonunit cofactor, its special pure output leaves both
ordinary short slots available for the at most two remaining
members of that group. Any remaining unit-cofactor original is
the top row; exclusion of γ from the new short digits makes its
inverse fine, so pure 81 suffices.

For q=37, every ordinary output is smaller than q²m, irrespective
of the original row. The three numerical signatures separate
all groups, and all outputs have ternary depth at least three,
so they are fresh against every retained original. The two
special outputs have the strict prices already used in CD65.
The two terminal leaves are fully paid, and every remaining source
inverse has one complete enclosure. The resulting
whole cover has unchanged class count and strictly smaller
modulus sum, contradicting global minimality.

There are therefore at most five free candidate digits. At
least 34−5=29 candidates have a repeated-digit triple at all five
words. Equal cofactors would give equal numerical top labels
9q²m, hence the same actual top original and the same (b,u).
Choosing witnesses for the 29-by-five cells therefore gives
145 distinct cofactors. They are nonunit: a unit bottom member
would be the actual pure q² original and would have digit b0,
which was excluded.

The remaining gap is to use this actual repeated-digit inventory
to obtain a complete compatible replacement, or another strict
whole-family descent. The count alone supplies neither common
cofactor incidence nor distinct prime divisors for its witnesses.

A complete scoped transient Lean check verifies this actual-family
implication through the six-cell selection, four-leaf code, complete
joint-hole source, grouped numerical allocation and whole-cover
minimality contradiction. It also verifies the 29-by-five witness
injection without an additional allocation or saturation premise.
All 59 reported axiom closures use only `propext`, `Classical.choice`
and `Quot.sound`; the complete check has no errors or `sorry`.
These are temporary applications of the existing minimality,
CRT and finite-combinatorial results, with no retained declaration,
freeze or coverage record. The verified conclusion is the literal
inventory CD69--70, not a common cofactor point or exclusion of 37.

## Paired low rows force a source-contacting top outside their divisor cones

Keep one actual globally count-then-modulus-sum-minimal distinct odd
nonunit whole cover, actual pure moduli 3 and 9, ternary heights at
most two, and the same coprime coordinate factorization with q=37.
Assume an actual q-height at least two. The conclusions above give
an actual pure q² original h, no q-height greater than two, and its
five-word private projection Λ. Write c for its first q-digit, b0
for its second digit, and D for all actual height-two originals
with first digit c. These conditions concern the original family;
comparison covers are not restricted to ternary height two.

Choose the saturated set T of at least 29 digits so that it also
avoids the second digits β and γ of any remaining unit-cofactor
middle and top originals in D. Missing unit originals impose no
condition, and β=γ is allowed. Both guards differ from b0. For a
terminal digit a in T, use all actual paired low rows at that digit:

$$
R_a=\{r>1:\text{the actual }q^2r\text{ and }3q^2r
\text{ originals both lie in }D\text{ and have second digit }a\}.
\tag{CD73}
$$

The pair's old cofactor phases need not agree. Nor does membership
in R_a require compatibility with a particular ternary word.
For a digit b and word u, let C(b,u) be the set of actual top
originals in D with second digit b and ternary phase u modulo 9.
SNC14 gives |C(b,u)|≤2. Retain the actual source condition

$$
i\in C^*(b,u)
\quad\Longleftrightarrow\quad
i\in C(b,u),\quad
\exists y\in P_h:\ y\equiv u\pmod9,\quad
 y\equiv\rho_i\pmod{m_i}.
\tag{CD74}
$$

Here P_h is the complete private region of the pure donor h.
This condition says that the original top cofactor class meets
that actual private section. It does not assert that y belongs
to the top original itself: its q-coordinate still belongs to h.

The following restriction is forced by the original whole cover:

$$
\forall a\in T,\quad
\forall b\notin\{b_0,a,\beta,\gamma\},\quad
\forall u\in\Lambda,\quad
\exists i\in C^*(b,u):\quad
\forall r\in R_a,\ r\nmid m_i.
\tag{CD75}
$$

Thus even after ignoring top classes that never meet the private
section, each allowed cell retains a top cofactor outside the
entire divisibility cone of the terminal's paired low rows.
This conclusion supplies a necessary arithmetic restriction;
it does not exclude 37 or provide a replacement for every cell.

### Four paid terminal pieces leave one short cell

Fix a, b and u from CD75. Saturation at a supplies five actual
nonunit top originals at distinct ternary words. Choose three
of them, h1,h2,h3, and assign the four pure replacement labels

$$
h\mapsto27,\qquad h_1\mapsto27q,\qquad
h_2\mapsto81,\qquad h_3\mapsto81q.
\tag{CD76}
$$

Choose four distinct leaves modulo 27 above Λ and assign them
b0,a,b,β; the leaf assigned b has parent u. Collapse each leaf's
three modulo-81 children to its assigned digit. The remaining
33 fine words receive distinct digits, giving 4+33=37 symbols.
The first two leaves are paid directly by 27 and 27q. The first
two fine children of the β leaf are paid by 81 and 81q. Only its
third child remains in the continuing source, so that digit's
remaining inverse is fine. The b leaf is the only continuing
inverse that needs an entire short leaf.

The code also makes the whole β fiber avoid the actual unit
middle ternary phase, and the whole γ fiber avoid the actual
unit top phase. When β=γ, choose the β leaf's parent outside
both forbidden sets; at most four of the five words are
forbidden. When the digits differ, assign γ a fine word outside
the four collapsed leaves and outside its forbidden top word.
Any remaining unit middle and top originals therefore have
empty continuing inverses. Give them the unused labels 243 and
243q, respectively, preserving the exact number of classes.
Their strict prices are 243<3q² and 243q<9q² at q=37.

Suppose CD75 fails. Every active top in C*(b,u) then has a
cofactor divisor in R_a. There are at most two such tops. Assign
them distinct members of their paired low-row donors, using
row zero for one and row one for the other. Even if the same
r pays both tops, its two physical donors have different labels
27r and 27qr. Both donors' former continuing inverses are empty
because their source digit a is already terminal-paid. Each
selected donor can therefore take the one permanent cofactor
phase required by its assigned top.

Use the original row labels 27m,27qm,81m for all other nonunit
outputs. The complete source preserves the same 9W coordinate
and first q-digit as in CD63. A top source owner at the short
b leaf has an actual witness y from that identity, so it belongs
to C*(b,u); its entire inverse is paid by the assigned divisor
output. Low-row inverses are already short-enclosed, and every
other unpaid top inverse is fine-enclosed. This uses the full
private section and all its points, not selected private witnesses
or a product envelope Λ×W.

Numerical labels remain injective: their coprime cofactor and
ternary/q exponents distinguish the nonunit signatures and all
six pure signatures. Every new label has ternary depth at least
three and is fresh against the retained family. Each replaced
original has a strictly smaller output label. Complete coverage
with unchanged class count therefore contradicts global
modulus-sum minimality, proving CD75.

### The same alternate top works for every divisor ancestor

Fix b in T and u in Λ. For a literal top i in C(b,u), define

$$
A(i)=\{a\in T\setminus\{b\}:\exists r\in R_a,
\ r\mid m_i\}.
\tag{CD77}
$$

If C(b,u) has one member, that member has no ancestors in A(i).
If it has two members i,j, their ancestor sets are disjoint.
Indeed, a common ancestor terminal would contradict CD75,
since there is no third top available to escape it.

More precisely, if A(i) is nonempty, there is one unique other
literal top j in the cell, it belongs to C*(b,u), and

$$
\forall a\in A(i),\quad\forall r\in R_a,\quad r\nmid m_j.
\tag{CD78}
$$

Choose an ancestor once. Its active escape witness differs from
i, hence determines j by the two-owner cap. Every later ancestor
must use that same j. Its private-section witness can also be
chosen once and held fixed across these terminals. No premise
requires i itself to meet the private section or j to belong to
a repeated-digit triple.

CD78 concerns numerical divisibility. The fixed private point
need not avoid the low owners' cofactor residue classes, and it need not
lie in i's cofactor class. A simultaneous payment using their
actual phases remains a separate obligation. The unrestricted
odd distinct covering problem and the entire ternary-height-two
branch remain unresolved.

A complete scoped transient Lean check verifies CD75 with all
original-family assumptions, including unit guards, finite code,
actual private-section contact, injective donor selection,
permanent phases, numerical legality and whole-cover descent.
It also derives CD78 from that same original telescope and the
existing two-owner cap. These applications reuse existing results;
no new mathematical declaration, freeze or coverage record is
retained. All 78 reported axiom closures use only `propext`, `Classical.choice`
and `Quot.sound`; the complete check has no errors or `sorry`.
## Two low-row families miss one common private point

Retain the actual-family assumptions, pure donor h, five-word
projection Λ, saturated set T and unit guards from CD73--75.
For a digit d, collect every actual low-row cofactor class at
that digit:

$$
L_d=\bigcup_{\substack{i\in D,\ a_i\le1\\b_i=d}}
\{y\in\mathbb N:y\equiv\rho_i\pmod{m_i}\}.
\tag{CD79}
$$

There is no old ternary-phase compatibility restriction in this
union. It includes both rows zero and one, with their actual
cofactor phases. The allowed digits exclude b0 and β, so these
low originals have nonunit cofactors.

For every a in T, every b outside {b0,a,β,γ}, and every u in Λ,
there is one actual private point simultaneously outside both
low-row families:

$$
\{y\in P_h:y\equiv u\pmod9\}\setminus(L_a\cup L_b)
\ne\varnothing.
\tag{CD80}
$$

Moreover, that same y meets actual top cofactor classes from
both digit cells:

$$
\exists i\in C(a,u),\ \exists j\in C(b,u):\quad
 y\equiv\rho_i\pmod{m_i},\qquad
 y\equiv\rho_j\pmod{m_j}.
\tag{CD81}
$$

The top originals are different because their second digits
are a and b. Their cofactor classes meet on the actual private
section. This does not say that their full original APs meet:
the two different q² digits make those APs disjoint.

### Fix all phases before removing the paid low rows

Use the same four direct terminal pieces and one continuing
short leaf as in CD76. For every output retaining an original
cofactor, keep its phase modulo that cofactor equal to the
original phase. The low originals at a
have no continuing inverse under the compressed source; their
outputs can be placed at the target short leaf. Low originals
at b already have any continuing inverse within that leaf.
The labels 27m and 27qm therefore cover their respective
cofactor classes throughout the leaf within the common first-q
cylinder c. Incompatible old ternary
phases cause no problem: the new ternary tag is chosen for this
leaf and preserves every old source liability.

Suppose the private u-section were contained in L_a union L_b.
For an unpaid top-source point on the short leaf, the exact
9W source identity supplies a private y with the same ternary
word and cofactor data. Choose the actual low owner at a or b
that covers y's cofactor coordinate. Its fixed output covers
the original target point as well. This choice may vary with
the point; the emitted label and phase of each owner stay fixed.
All other source points have the complete payments already
established in CD76. Numerical distinctness, freshness, equal
count and strict sum decrease give the same global minimality
contradiction, proving CD80.

Take y from CD80 and separately insert digit a and digit b into
its q² coordinate while preserving its complete 9W coordinate
and first q-digit c. Each transported point lies in the same
complete deletion hole, so an actual original in D covers it.
A low-row owner would put the unchanged y into L_a or L_b,
contradicting its selection. Both owners are therefore top
rows and have ternary word u, giving CD81 with this one y.

The auxiliary low outputs at a are part of the fixed payment.
A later reallocation that changes or removes one of them must
preserve its auxiliary coverage, even though its primary
compressed-source inverse was empty. Otherwise the residual
used in CD80 would no longer correspond to the emitted family.

This is a statement about every allowed pair of digits. It
does not produce one private point or one set of top owners
working for all digit pairs simultaneously. Distinct fresh
labels and affordable total cost for a replacement of the
remaining top intersections are still required; CD80--81 alone
give no contradiction for the original whole cover.

A complete scoped transient Lean check verifies the pointwise
fixed-phase payment, the nonempty simultaneous residual, and
both actual top contacts from the original family assumptions.
No low-coverage, shared-point or allocation condition is added
to the final theorem. The earlier CD75 and CD78 consumers are
also checked against the generalized pointwise payment.
All 82 reported axiom closures use only `propext`, `Classical.choice`
and `Quot.sound`; the complete check has no errors or `sorry`.
These are transient applications of existing results, with no retained
mathematical declaration, freeze or coverage record.
## Three-child payment excludes the q=37 square layer

Let F be one actual globally count-then-modulus-sum-minimal finite
cover by distinct odd nonunit moduli. Assume that F contains the
actual moduli 3 and 9, every original has ternary height at most
two, and its moduli have the common coordinate factorization

$$
d_i=3^{a_i}37^{j_i}m_i,\qquad
 a_i\le2,\quad m_i\mid W,\quad W>0,\quad\gcd(W,111)=1.
\tag{CD82}
$$

Then no original has $j_i\ge2$. Equivalently, the 37 direction
has height at most one under these assumptions. The comparison
covers used by global minimality may have higher ternary height.
This excludes the square layer at 37; it does not exclude
originals divisible by 37, the entire ternary-height-two branch,
or an unrestricted odd distinct covering system.

Suppose instead that an actual deep original exists. The
previous actual-family constructions supply the pure donor
$h$ of modulus $37^2$, the five-word private projection
$\Lambda$, the unit guard digits, and at least 29 safe digits
saturated at all words of $\Lambda$. Set $q=37$ and let
$c=\rho_h\bmod q$ be the donor's first-q phase. Choose two different such
digits $a,b$ and any $u\in\Lambda$. Write

$$
 A=C(a,u),\qquad B=C(b,u),\qquad |B|\le2.
\tag{CD83}
$$

Choose three distinct top originals at a whose old ternary
words differ from u, and use them for the direct outputs
$27q,81,81q$ in CD76. Choose three distinct top originals at b
whose old ternary words also differ from u, and call this
three-element set O. Each choice is available from the four
other saturated words. The pure donor supplies the direct
output 27. All these choices refer to actual originals in
the same cover.

Use the existing guarded code with a as its terminal digit and
b as its continuing short digit. Let $z\bmod27$ be that short
leaf, with $z\bmod9=u$. Its three children are

$$
 z,\quad z+27,\quad z+54\pmod{81}.
\tag{CD84}
$$

Keep every original low-row output at both a and b in its
original cofactor phase, with ternary tag z modulo 27. Keep all other
normal outputs except O. Set the normal top tags for B to z
and those for A to $z+27$. Add one output for each $i\in B$
with modulus $81qm_i$, ternary tag $z+54$, first-q phase c,
and original cofactor phase $\rho_i\bmod m_i$.

### Coverage of the complete deletion hole

Every point x in the exact hole has first-q phase c and one
actual private point y satisfying $y\equiv x\pmod{9W}$.
Outside the continuing short leaf, the original guarded source
map gives the existing direct or normal payment. Its continuing
owner has second digit different from a and b, so it cannot
belong to O, and its normal tag is unchanged.

On the short leaf, $y\bmod9=u$. If y lies in a low cofactor
class at a or b, the corresponding preserved low output pays
x throughout the leaf. Otherwise insert a or b into y's
second q digit while preserving its entire 9W coordinate.
The exact-hole identity and actual whole cover then supply
a top cofactor class in A and one in B. These facts hold for
every private y in the residual, not only for one selected
contact point. The three child payments are

$$
\begin{array}{c|c|c}
 x\bmod81 & \text{actual cofactor family} & \text{output modulus}\\
 \hline
 z & B & 81m_i\\
 z+27 & A & 81m_i\\
 z+54 & B & 81qm_i.
\end{array}
\tag{CD85}
$$

The last output's first-q condition is already satisfied by
every point in the hole. No product of two cofactors or common
intersection of their original q-squared APs is needed. The
three a terminals lie outside u, so none consumes an A output.
Every omitted owner in O has digit b and an old word different
from u: it has no continuing inverse outside the short leaf
and cannot be the needed B top inside it. No low output is
omitted or rephased.

### Distinct labels and strict count decrease

The normal nonunit output signatures are $27m,27qm,81m$.
All normal outputs remain injective by the existing output-label
result. The unit backups $243,243q$ have ternary height five,
different from the other output signatures.
The added $81qm$ signature is different from all three because
$m$ is coprime to $3q$. Its only pure counterpart is the
special output $81q$, and the safe digit b excludes cofactor
one. Distinct members of A and B have distinct cofactors:
their original moduli are the distinct labels $9q^2m$.
Every replacement label is odd, greater than one, and divisible
by 27, so none coincides with a retained original.

If D is the complete original deletion set, the replacement
index set is the disjoint union

$$
 J=(D\setminus O)\sqcup B,\qquad
 |J|=|D|-3+|B|\le |D|-1.
\tag{CD86}
$$

Thus the unchanged originals together with J form a full
integer cover with fewer distinct odd nonunit moduli than F.
This contradicts its global count minimality and proves the
claim in CD82. The final step requires no modulus-sum estimate.

A complete scoped transient Lean check verifies the outside-word
selections, every point of the source payment, all output labels,
strict count decrease, and the final contradiction from the original
family assumptions in CD82. The final theorem assumes no supplied
saturation, contact, allocation or replacement condition. All 86
reported axiom closures use only `propext`, `Classical.choice` and
`Quot.sound`; the complete check has no errors or `sorry`. These
are exact applications of existing results, with no retained
mathematical declaration, freeze or coverage record.
### Multiple paired leaves exclude every square layer at q at least 29

Fix one globally count-then-modulus-sum minimal finite distinct odd
nonunit whole cover F. Assume its original ternary heights are at most
two and that the numerical labels 3 and 9 occur in F. For a prime
$q\ge29$, use the actual factorization
$d_i=3^{a_i}q^{j_i}m_i$, with $m_i\mid W$, $W>0$ and $(W,3q)=1$.
Then

$$
\boxed{j_i\le1\quad\text{for every actual original }i.}
\tag{CD87}
$$

This includes 29 and 31 as well as the primes covered by CD68 and
CD82. It does not remove height-one q-originals, and it retains the
ternary-height and pure-guard hypotheses.

Suppose an actual original has q-height at least two. CD47 excludes
height three, numerical divisor closure supplies an actual pure
$q^2$ original h, and CD65 gives

$$
\Lambda=\Lambda_h,\qquad s=|\Lambda|\in\{4,5\}.
\tag{CD88}
$$

Let D consist of all actual height-two originals whose first q-digit
is $c=\rho_h\bmod q$. Let U be the set of second q-digits of all
unit-cofactor originals in D. There are at most three such originals:
for each row $a_i\in\{0,1,2\}$, cofactor one determines the numerical
label $3^{a_i}q^2$, and the original labels are distinct. Thus
$|U|\le3$, and U includes the second digit of h.

The rooted-component inventory CD56 supplies at least $q-14$ second
digits with actual top-row owners in D. Removing U leaves at least
$q-17$ of them. Choose disjoint digit pairs $(a_t,b_t)$ outside U,
with an actual top owner at every $a_t$, using

$$
r=\begin{cases}4,&s=4,\\11,&s=5.\end{cases}
\tag{CD89}
$$

There are enough choices because $r\le q-17$ and $2r\le q-3$.
No positive top count is required at $b_t$.

For any digit d, let $n(d)$ count all actual top owners in D at d,
including owners whose old word lies outside $\Lambda$. Let
$C(d,u)$ be their subfamily with old residue $u\pmod9$. Define

$$
g_t(u)=n(a_t)+n(b_t)-|C(a_t,u)|-2|C(b_t,u)|.
\tag{CD90}
$$

Each pair has at most one word with $g_t(u)\le0$. Indeed, for distinct
u and w the two a-cells are disjoint, as are the two b-cells. If both
words had nonpositive gain, summing those inequalities would force
$n(a_t)\le0$, contrary to its actual witness.

### A matching chooses good leaves and one reserved word

Choose a reserved word $v\in\Lambda$. Its three modulo-27 parents
are $v,v+9,v+18$. The first two will receive the pure outputs 27
and $27q$. The first two modulo-81 children of the third parent
will receive 81 and $81q$, leaving only the child $v+72$ for the
ordinary source map.

For $s=4$, every pair has at least six good parents outside v,
so four distinct good parents can be chosen. For $s=5$, there are
twelve parents outside v, and each pair has at least nine good ones.
A Hall obstruction among eleven pairs could only involve at least
ten pairs sharing the same bad word outside v. At most one word
can be bad for ten pairs, because every pair has at most one bad
word. Choose that word as v if it exists, and otherwise choose any
word of $\Lambda$. Every Hall inequality then holds.

Thus the pairs receive distinct parents $z_t$ outside v with
$u_t=z_t\bmod9\in\Lambda$ and $g_t(u_t)\ge1$. Collapse each parent
$z_t$ to source digit $b_t$, and leave every $a_t$ unused. Also leave
all digits of U unused. Apart from the reserved pure pieces, the
number of active source pieces is

$$
9s-8-2r\le q-3-r.
\tag{CD91}
$$

The right side is a lower bound for the available digit count after excluding U and
all a-digits. The b-digits serve their prescribed collapsed parents;
all other active pieces receive distinct unused digits. Equivalently,
after also removing the b-digits there are $9s-8-3r$ ordinary fine
pieces and at least $q-3-2r$ digits. CD91 follows from $q\ge29$ in
both cases of CD89. Every changed unit original has an empty active
inverse; no phase-specific placement of unit digits is required.

### Original phases, complete coverage and the count saving

Let $O_{\rm all}$ consist of all paired-digit top owners outside
their pair's selected word. Set

$$
C=\bigcup_t C(b_t,u_t),\qquad
|O_{\rm all}|-|C|=\sum_t g_t(u_t)\ge r.
\tag{CD92}
$$

Choose three distinct members $h_1,h_2,h_3$ of $O_{\rm all}$ for the
pure outputs $27q,81,81q$; h supplies 27. The three chosen owners
may come from different pairs and from either side of a pair.
Disjoint pair digits ensure that none belongs to any selected a-
or b-cell. Omit the remaining set
$O=O_{\rm all}\setminus\{h_1,h_2,h_3\}$.

Keep every paired low-row output in its original cofactor phase,
with its pair's tag $z_t\pmod{27}$. On that parent use the three
child payments of CD85: the selected b-cell at $z_t$ via $81m_i$,
the selected a-cell at $z_t+27$ via $81m_i$, and a duplicate of the
b-cell at $z_t+54$ via $81qm_i$. Each owner belongs to at most one
pair, so it receives only one auxiliary low-row promise and one
fixed tag.

For every point in the complete deletion hole, the exact source
identity supplies a private y with the same full $9W$ coordinate.
On a paired parent, a preserved low cofactor class pays the point
if one is present. Otherwise inserting either paired second digit
into that same y supplies the required actual top class in each
selected cell. This proves payment for every residual point. Off
all paired parents, the source uses neither side of a pair, so its
ordinary owner is not omitted. The reserved pieces are paid by the
four pure outputs. No common private point across different pairs
or different target integers is assumed.

All labels are distinct by the same coprime signatures as CD85:
normal nonunit labels $27m,27qm,81m$, extra labels $81qm$, the four
pure labels, and unit backups $243,243q$. Paired digits avoid U,
so no extra has cofactor one. Equality between two extra cofactors
would imply equality of their old labels $9q^2m$, hence equality of
the old indices. Every output is odd, greater than one and divisible
by 27; all retained originals have ternary height at most two.

The unchanged originals together with the replacements therefore
form a distinct odd nonunit whole cover, with class-count change

$$
-|O|+|C|=3-\sum_t g_t(u_t)\le3-r<0.
\tag{CD93}
$$

This contradicts global count minimality. The construction uses
neither a cell-size-two bound nor saturated digits. Its antecedent
suppliers still use the full stated count-then-sum minimality.

The complete scoped transient Lean application checks CD87 directly
from the original family assumptions, including actual pair supply,
Hall selection, the finite code, all cofactor phases, whole coverage,
label injectivity and strict count decrease. All 108 axiom reports
use only `propext`, `Classical.choice`, `Quot.sound`, or a subset of
these; the command exits successfully with no errors or `sorryAx`.
It reuses existing source and finite-set results, including Mathlib's
finite Hall theorem. No new retained declaration, freeze or coverage
record is introduced. The square layers at smaller primes and the
unrestricted-height problem remain unresolved.
### A squared 23 forces the full five-word private projection

Keep the original family assumptions of CD87, but take $q=23$.
If an actual original has q-height at least two, the actual pure
$q^2$ original h supplied by divisor closure satisfies

$$
\boxed{|\Lambda_h|=5.}
\tag{CD94}
$$

The conclusion is a projection restriction. It does not exclude
$q^2$ itself. CD65 already gives $|\Lambda_h|\in\{4,5\}$, so it
suffices to rule out four words.

Assume $s=4$. Use the same unit-digit exclusion set U as in CD88,
and write E for all safe digits outside U. Let P be the full set
of digits in E with at least one actual top owner in D. This is
the full top support, rather than merely the rooted-component image
used to bound it. CD56 gives

$$
|E|\ge20,\qquad |P|\ge6.
\tag{CD95}
$$

Choose eight disjoint pairs outside U. If $|P|\ge8$, give every
pair a positive a-digit and choose its b-digit from the remaining
safe digits. If $|P|<8$, place every member of P among the a-digits,
fill the remaining a-positions with digits outside P, and choose all
b-digits outside these eight a-digits. Then at least six pairs have
a positive a-count. Every remaining pair has no top owners on either
side, because all safe top-positive digits have already been placed
among the a-digits.

For positive pairs use the strict-good-word condition CD90. For a
pair with no top owners on either side, allow every word and assign
gain zero. Such a pair makes no contribution to either the omitted
or duplicated top families; it remains a lawful source operation
because the original low-row outputs are retained.

The leaf matching extends to eight pairs on four words. After one
reserved word v is removed there are nine parents, and every pair
has at least six allowed parents. Choose v to be a word forbidden
by at least seven pairs, if one exists. There can be at most one
such word among eight pairs. Hall subsets of size at most six fit
inside a single menu; every larger subset then reaches all nine
parents. This gives eight distinct allowed parents.

For this choice the active code has exactly the required capacity:

$$
9s-8-2r=12=23-3-r,
\qquad s=4,\ r=8.
\tag{CD96}
$$

The whole-source payment and label comparison from CD92--CD93 apply
unchanged. Positive pairs each contribute at least one unit of net
top saving, and all other pairs contribute zero. Keeping three
omitted owners for the pure outputs therefore changes the class
count by at most

$$
3-\sum_{t=1}^{8}g_t(u_t)\le3-6=-3.
\tag{CD97}
$$

The resulting distinct odd nonunit whole cover contradicts global
count minimality. Thus the four-word case is impossible and CD94
follows. The proof supplies its positive and zero-top pairs from the
actual original family; it assumes no extra inventory or allocation.

A complete scoped transient Lean application checks the conclusion
from the original family, pure 3 and 9 guards, $q=23$ and an actual
deep original. It constructs an actual pure $q^2$ original with
row zero, height two, cofactor one and private projection of size
five. All 115 axiom reports use only the same standard axioms as
CD87, with no errors or `sorryAx`. No new retained declaration,
freeze or coverage record is introduced. The five-word case at 23,
the smaller prime square layers, and unrestricted Erdős #7 remain
unresolved.

### A squared 23 needs top owners at sixteen safe second digits

Retain the assumptions and the actual pure $q^2$ original h of CD94.
Use $D$ and $U$ from CD88: D contains the height-two originals with
the same first q-digit as h, while U contains the second digits of
the unit-cofactor originals in D. Define the complete safe top support
and its complement by

$$
P=\{d\notin U:n(d)>0\},\qquad
Z=\{d\notin U:n(d)=0\}.
\tag{CD98}
$$

Then

$$
\boxed{|Z|\le4,\qquad |P|\ge16.}
\tag{CD99}
$$

Each counted digit has an actual row-two original in D, with its
original cofactor and phase. This is a digit inventory; it does not
assert that these original classes meet at one point or have a
common cofactor. The same bound holds if U is enlarged to any set
of at most three digits containing all the unit digits.

Suppose instead that there are five distinct digits in Z. Reserve
five of them for individual short parents. At least fifteen safe
digits remain. Removing top-free digits does not remove any positive
top digit, so the CD56 inventory used in CD95 still supplies at least
six positive digits among them. Choose seven disjoint pairs using the same positive-first,
zero-filler rule as in CD95. At least six pairs have positive a-count;
every other pair has no top owners on either side.

Assign the seven pairs and five individual digits to the twelve
modulo-27 parents outside one reserved word v. A pair allows all
but at most one word, and an individual top-free digit allows every
word. The same finite Hall construction gives distinct parents for
all twelve assignments. Reserve the four pure pieces above v as
in CD91.

The seven a-digits remain unused by the ordinary source map. The
seven b-digits and five individual digits each encode their assigned
whole parent. Only one fine piece above v remains. The alphabet
calculation is

$$
45-8-2\cdot12=13=23-3-7.
\tag{CD100}
$$

Thus all thirteen active pieces receive legal source digits while
all unit digits and all seven a-digits stay unused.

An individual top-free digit needs no additional top output. Insert
it into the private source while preserving the entire $9W$
coordinate. The exact-hole identity and the original whole cover
supply an actual owner in D. It cannot have row two, by the definition
of Z. Its existing row-zero or row-one output therefore pays the
whole assigned modulo-27 parent, using its one fixed tag and original
cofactor phase. This argument applies separately to every target
point; it does not posit a common low owner for the whole parent.

The paired parents use the three-child payments of CD85, and all
remaining source and retained-family cases are unchanged. Only
paired top owners are omitted or duplicated. The seven pairs have
at least six units of total gain, so after reserving three actual
top owners for the pure outputs the count change again satisfies

$$
-|O|+|C|\le3-6=-3.
\tag{CD101}
$$

No new numerical output type is needed for an individual top-free
digit. The original row and cofactor still recover its normal output
label, so label distinctness and freshness follow from the same
whole-family comparison as CD93. The resulting strictly smaller
whole cover is impossible. Therefore $|Z|\le4$, and $|U|\le3$
gives $|P|=23-|U|-|Z|\ge16$.

A complete scoped transient Lean application checks both the bound
for every such U and its construction from the original globally
count-then-modulus-sum-minimal family, pure 3 and 9, original ternary
heights at most two, $q=23$ and an actual deep original. All 121 axiom
reports use only `propext`, `Classical.choice` and `Quot.sound`, with
no errors or `sorryAx`. No new retained declaration, freeze or
coverage record is introduced. This does not exclude the five-word
case at 23, the smaller prime square layers, or unrestricted Erdős #7.

### A squared 19 needs four or five private ternary words

Keep the original global count-then-modulus-sum-minimal distinct odd
nonunit whole cover F, actual pure moduli 3 and 9, and original
ternary heights at most two. Use the same factorization, positive
W and coprimality assumptions as CD87, now with $q=19$. If an actual
original has q-height at least two, an actual pure $q^2$ original h
exists and satisfies

$$
\boxed{|\Lambda_h|\in\{4,5\}.}
\tag{CD102}
$$

The two-terminal capacity bound CD65 already leaves only three,
four or five words. Suppose there are three. CD56 gives at least
five top-positive second digits. Removing the unit digits U leaves
at least two positive digits and at least sixteen safe digits in
all. Apply the positive-first, zero-filler selection to obtain five
disjoint pairs $(a_t,b_t)$. At least two have positive a-count;
every other pair has zero top count on both sides. Declare every
word good for a zero pair and use the strict inequality of CD90
for a positive pair. Write its guaranteed gain as $\varepsilon_t$:

$$
\varepsilon_t\in\{0,1\},\qquad
\sum_{t=1}^{5}\varepsilon_t\ge2,\qquad
|C(a_t,u_t)|+2|C(b_t,u_t)|+\varepsilon_t
\le n(a_t)+n(b_t).
\tag{CD103}
$$

The finite Hall construction supplies five distinct good
modulo-27 parents outside one reserved private word v. Above v,
reserve only two parents, for pure outputs 27 and 27q. Leave its
third parent in the ordinary active code. Thus there are seven
active parents: five collapsed pair parents and two ordinary
parents, each of the latter split into three fine pieces.

The code therefore needs eleven symbols: five b-digits for the
paired parents and six other digits for the remaining fine pieces.
It avoids U and all five a-digits. The exact capacity is

$$
9\cdot3-6-2\cdot5=11=19-3-5.
\tag{CD104}
$$

Pair low outputs keep their original cofactor phases and their
assigned parent. For a residual target in that parent, the three
children are paid by the b-top output $81m$, the a-top output $81m$,
and one extra b-top output $81qm$, respectively, as in CD85. The
source preserves the entire $9W$ coordinate. The ordinary fine
pieces and unchanged originals use the same exact-hole argument.
There are no pure 81 or 81q outputs in this construction.

Let $O_{\rm all}$ be all paired top owners outside their selected
word and C the b-top owners at their selected word. Equation CD103
gives $|O_{\rm all}|-|C|\ge2$. Retain one actual member of
$O_{\rm all}$ as the pure 27q donor; h supplies pure 27. Delete the
other members and duplicate precisely C. The total class-count
change is at most

$$
1-|O_{\rm all}|+|C|\le1-2=-1.
\tag{CD105}
$$

All ordinary nonunit labels remain $27m,27qm,81m$, extras are
$81qm$, and unused unit owners use $243,243q$. Their ternary and
q-exponents, together with their cofactor, recover the original
numerical label; pair digits outside U ensure that extras have
nonunit cofactor. All replacement labels are distinct odd nonunits
and divisible by 27, hence fresh against the retained shallow
originals. This constructs a strictly smaller whole cover and
contradicts global count minimality, excluding the three-word case.

A complete scoped transient Lean application checks CD102 from the
original family and an actual deep original, including pair supply,
finite code, source coverage, label legality and the strict count
comparison. Its 130 axiom reports use only `propext`,
`Classical.choice` and `Quot.sound`, with no errors or `sorryAx`.
No new retained declaration, freeze or coverage record is introduced.
The four- and five-word cases at 19, complete exclusion of its square
layer, the whole ternary-height-two branch, and unrestricted Erdős #7
remain unresolved.

### Sixteen safe digits must each occur at four private words

Retain the original-family assumptions at $q=23$ in CD94, and the
actual pure $q^2$ original h and unit-digit set U supplied in CD99.
For each safe digit d define its empty private-word cells by

$$
E(d)=\{u\in\Lambda:C(d,u)=\varnothing\}.
\tag{CD106}
$$

Then the stronger distribution constraint is

$$
\boxed{
\#\{d\notin U:|E(d)|\ge2\}\le4,\qquad
\#\{d\notin U:\#\{u\in\Lambda:C(d,u)\ne\varnothing\}\ge4\}\ge16.
}
\tag{CD107}
$$

The cells contain actual original top owners with their own cofactors
and phases. No common owner, common cofactor or simultaneous meeting
point is asserted across cells.

Suppose five distinct safe digits $d_1,\ldots,d_5$ each had at least
two empty private-word cells. Removing them leaves at least fifteen
safe digits and, by CD99, at least eleven top-positive digits. Choose
seven disjoint pairs with every a-digit top-positive. All endpoints
avoid the five individual digits. Each pair has at most one bad
private word for the strict gain inequality CD90.

There is a joint assignment of the seven pairs and five individual
digits to twelve distinct modulo-27 parents outside one private
word v. A pair is assigned at a good word; an individual digit is
assigned at one of its empty cells. The reservation can be verified
directly by Hall's condition. Put

$$
\begin{aligned}
b(u)&=\#\{t:u\text{ is bad for pair }t\},\\
h(u)&=\#\{j:u\notin E(d_j)\},\\
m(v,u)&=\#\{j:E(d_j)=\{v,u\}\}.
\end{aligned}
\tag{CD108}
$$

Choose v so that for every other private word u, $m(v,u)\le3$ and
either $b(u)\le4$ or $h(u)\le2$. Such a choice exists: at most one
word is bad for five or more pairs. If four or more individual hole
sets equal the same two-element set, reserve a word outside that
set, choosing the heavy bad word itself when it is outside. At an
endpoint of that hole pair, at most one individual menu omits the
word. If no hole pair occurs four times, reserve the heavy bad word
when one exists, and otherwise any private word.

After reserving v, each pair has at least nine available parents
and each individual digit at least three. A set of at most nine
requests containing a pair satisfies Hall immediately. Four or
five individual requests cannot all be confined to one word,
because $m(v,u)\le3$; smaller individual sets fit one menu. Any set
of ten or more requests has at least five pairs and three individuals.
If its union omitted a remaining word u, both $b(u)\ge5$ and
$h(u)\ge3$ would hold, contrary to the choice of v. Its union therefore
contains all twelve parents. This proves the joint assignment.

Use the same thirteen-symbol mixed code as CD100. At a parent
assigned to $d_j$, the source preserves the complete $9W$ coordinate
and inserts $d_j$. If its actual covering owner had row two, that
owner would belong to the selected empty cell $C(d_j,u_j)$, a
contradiction. For each target point in that parent, an actual low owner
supplies coverage at its own original phase. Tops at other words for this individual digit are
not omitted and require no extra output.

The seven pairs each supply at least one unit of gain. Omissions
and duplications are still confined to paired top owners. Retaining
three omitted owners for the pure outputs gives

$$
-|O|+|C|\le3-7=-4.
\tag{CD109}
$$

The unchanged label comparison constructs a strictly smaller
whole cover, a contradiction. Thus at most four safe digits have
two or more empty private-word cells. Since there are at least
twenty safe digits and exactly five private words, at least sixteen
digits each have top owners at four or more private words.

A complete scoped transient Lean application checks CD107 from the
original globally count-then-modulus-sum-minimal whole family,
pure 3 and 9, original ternary heights at most two, $q=23$ and an
actual deep original. Its 135 axiom reports use only `propext`,
`Classical.choice` and `Quot.sound`, with no errors or `sorryAx`.
No new retained declaration, freeze or coverage record is introduced.
The remaining five-word case at 23 and unrestricted Erdős #7 remain
unresolved.

### A squared 17 also needs four or five private ternary words

Keep the original globally count-then-modulus-sum-minimal distinct
odd nonunit whole cover F, actual pure moduli 3 and 9, original
ternary heights at most two, and the factorization, positive W
and coprimality assumptions of CD87. At $q=17$, an actual original
of q-height at least two implies an actual pure $q^2$ original h
with

$$
\boxed{|\Lambda_h|\in\{4,5\}.}
\tag{CD110}
$$

The two-terminal capacity bound leaves only sizes three, four and
five. To exclude three, let U be the actual unit-cofactor digit
set, of size at most three, and let

$$
P=\{d\notin U:n_d>0\}.
\tag{CD111}
$$

The pure original h has second digit $\alpha\in U$. No Changed
top original can have that digit: it would be contained in h.
Consequently $n_\alpha=0$. The component support bound gives at
least three top-positive digits, and removing U removes at most
two of them. Thus $|P|\ge1$.

If $|P|\ge4$, choose five disjoint safe pairs, at least four with a
top-positive a-digit and any remaining pairs with both top sets
empty. The general parent matching assigns these pairs good
parents outside one reserved private word. The four-pure-output
code fits because

$$
9\cdot3\le17+5+5.
\tag{CD112}
$$

At least four units of pair gain remain. Retaining three omitted
top owners for the pure outputs still gives a strict reduction
in the number of classes.

If $1\le|P|\le3$, choose seven disjoint safe pairs. Every positive
a-digit belongs to a distinguished set G of at most three pairs;
the other pairs have two empty top sets. Reserve only two
modulo-27 parents for the pure outputs 27 and $27q$. Seven parents
remain. A pair in G forbids at most one private word, so even
after these reservations it has at least four available parents.
Every other pair allows all seven parents. Hall's condition holds:
a subset of at most four requests fits the menu of one request,
and a subset of five or more includes a request with the full
seven-parent menu.

Each of the seven parents is then collapsed to its own b-digit.
The two-pure code fits exactly:

$$
9\cdot3=17+3+7.
\tag{CD113}
$$

The pair gain is at least one. Retaining one omitted owner for
the second pure output gives a replacement with no more classes
than F. This branch needs the modulus-sum part of minimality.
Use unit backup labels 81 and $81q$. For nonunit cofactor m, the
ordinary outputs in rows zero, one and two have moduli $27m$,
$27qm$ and $81m$. A duplicated b-top receives $81m$ and $81qm$
together. At $q=17$ the comparisons are

$$
27<289,\qquad459<867,\qquad81<2601,\qquad
81(1+17)=1458<2601.
\tag{CD114}
$$

The pure output replacing h is smaller than $q^2$; the second
pure output is smaller than its retained top donor. Unit backups
are smaller than their original row-one and row-two moduli.
Numerical label signatures keep every replacement label distinct,
and the source construction retains each actual cofactor phase.
All retained unchanged originals keep their old moduli. Thus the
whole replacement has strictly smaller modulus sum. If its class
count drops, count minimality is contradicted; otherwise its
smaller sum contradicts the second stage of global minimality.
This excludes size three in both cases.

A complete scoped transient Lean application checks CD110 from
the original family assumptions and an actual deep original. Its
138 axiom reports use only `propext`, `Classical.choice` and
`Quot.sound`, with no errors or `sorryAx`. No new retained
declaration, freeze or coverage record is introduced. The
four- and five-word cases at 17, the entire ternary-height-two
branch and unrestricted Erdős #7 remain unresolved.

### Vacant lower slots force a rectangle of numerical triples

Retain the original-family assumptions of CD94 at $q=23$, with
pure h, five private words $\Lambda$, and a set U of at most three
digits containing every actual unit-cofactor digit. The following
condition uses the entire deleted family D, not just one cell:

$$
\begin{aligned}
\operatorname{Clean}(d,u)\iff
\forall i\in C(d,u),\quad&
\neg\exists j\in D:\ \operatorname{row}(j)=0,\ m_j=m_i\\
&\quad\lor\quad
\neg\exists j\in D:\ \operatorname{row}(j)=1,\ m_j=m_i.
\end{aligned}
\tag{CD115}
$$

The disjunction is inside the universal quantifier. Each actual
top owner may use a different vacant lower slot. An empty cell is
clean. A cell that is not clean contains an actual top cofactor m
whose two lower numerical companions both occur somewhere in D.
Their second digits and cofactor phases need not equal those of
the top owner.

For a fixed nonunit cofactor m, there are at most three Changed
owners, one per ternary row, because their original moduli are
$m q^2$, $3m q^2$ and $9m q^2$. Give them distinct slots from

$$
27m,\qquad27qm,\qquad81m.
\tag{CD116}
$$

Every low owner needs one of the first two slots. A top owner at
a selected clean cell also needs one of those slots. Cleanliness
ensures that no group demands three short slots. The existing
three-row slot-assignment theorem therefore assigns all groups
simultaneously. Labels in different groups remain distinct by
coprimality with $3q$. A top can exchange row roles with a lower
owner without exchanging their cofactor phases.

A single source digit can now serve a whole modulo-27 parent at
a clean cell: every target point has its own actual covering
owner, which receives a short slot if it is low or belongs to
that selected cell. The source insertion preserves the complete
$9W$ coordinate. The same grouping also supports the earlier
paired parents: their three modulo-81 children are still paid by
b, a and the extra b-output. The extra modulus $81qm$ occupies a
separate slot signature. No common cofactor witness is assumed.

Suppose five distinct safe digits could be assigned five distinct
parents at clean cells. At most three parents can have any one
private word. Removing these five digits leaves at least fifteen
safe digits and at least eleven top-positive digits by CD99.
Choose seven disjoint pairs, each with a top-positive a-digit.
For every pair, at least twelve of the fifteen parents lie at good
words. Removing the five clean parents leaves at least seven
choices. Hall's theorem assigns distinct parents to all seven
pairs. The three unassigned parents carry the four pure outputs:
two whole parents and two children of the third.

The remaining code consists of twelve collapsed parents and one
fine cell. Seven pairs supply at least seven units of gain;
retaining three top donors leaves a class-count decrease of at
least four. The grouped source, label comparison and whole-cover
construction therefore imply

$$
\boxed{\nu\le4,}
\tag{CD117}
$$

where $\nu$ is the maximum number of distinct safe digits that can
be assigned clean cells, with capacity three at each private word.
The three pure parents need not lie above the same private word.

Write $E=(\mathbb Z/q\mathbb Z)\setminus U$ and, for $V\subseteq\Lambda$,

$$
N(V)=\{d\in E:\exists u\in V,\ \operatorname{Clean}(d,u)\}.
\tag{CD118}
$$

A finite Hall argument gives a useful form of the obstruction.
Attach ten universal dummy digits to the fifteen parent slots.
A matching covering all slots would use at least five real digits,
contradicting CD117. Thus a deficient subset K of slots has word
projection V satisfying

$$
|N(V)|+10<|K|\le3|V|.
\tag{CD119}
$$

Since $|V|\le5$, either $|V|=4$ and $|N(V)|\le1$, or $V=\Lambda$
and $|N(V)|\le4$. Removing $N(V)$ from E gives a blocked rectangle
$T\times V$ of one of the two sizes

$$
\boxed{
|T|\ge19,\ |V|=4
\quad\text{or}\quad
|T|\ge16,\ |V|=5.
}
\tag{CD120}
$$

Every cell of this rectangle supplies an actual numerical triple
$m q^2,3m q^2,9m q^2$ in D. Different cells supply different
cofactors: equal cofactors would give equal top moduli, hence the
same original top owner and the same cell. All these cofactors
are nonunit and divide W. Consequently there are at least 76
distinct such cofactors; the second alternative gives at least 80.
This is a numerical triple condition, not the stronger C1
condition that places all three owners at one digit and word.

A complete scoped transient Lean application checks the blocked
rectangle and distinct-cofactor conclusion from the original
family assumptions and an actual deep original. Its 155 axiom
reports use only `propext`, `Classical.choice` and `Quot.sound`,
with no errors or `sorryAx`. It reuses the existing grouped-slot
result and Mathlib's finite Hall theorem. No new retained
declaration, freeze or coverage record is introduced. A joint
exchange using the companion locations, and exclusion of the
remaining squared-23 branch, remain unresolved.

### Four-word occupancy strengthens the bound to eighty triples

Under the same original-family assumptions, take U to be exactly
the second-digit image of all Changed unit-cofactor owners. The
stronger obstruction is $\nu\le3$ for this safe set. Two features
of the actual source make this improvement possible.

First, CD107 supplies at least sixteen safe digits whose top
owners occupy four or more private words. Replacing the previous
unit-containing set by the exact image only enlarges the safe
set. For any such a-digit and any private word u, at least three
actual top owners lie at other words. Since every b-cell has at
most two top owners,

$$
\begin{aligned}
n_a-|C(a,u)|&\ge3,\\
n_b-2|C(b,u)|&\ge-2,\\
g_{a,b}(u)&\ge1.
\end{aligned}
\tag{CD121}
$$

Thus these pairs are good at every private word. Given four clean
digits, remove them and select eight disjoint pairs with dense
a-digits; at least twelve dense digits and sixteen safe digits
remain available. Assign the four clean parents first. After
choosing a third pure parent for the one remaining fine cell,
there are ten other parents, from which eight arbitrary distinct
pair parents can be chosen. The other two parents carry the pure
modulo-27 outputs. No common reserved private word is needed.

Second, the boundary code can use the actual size of its forbidden
digit set $U'$ rather than the worst-case size three. With eight
unused a-digits and twelve collapsed parents, its capacity
condition is

$$
9\cdot5+8+|U'|\le23+8+2\cdot12,
\qquad\text{equivalently }|U'|\le2.
\tag{CD122}
$$

If $|U|\le2$, use $U'=U$. If $|U|=3$, the exact unit image has
three actual owners with distinct rows and distinct digits.
Let $\beta$ be the digit of its row-one owner g. There are at
least two private words outside g's modulo-3 phase, hence at
least six eligible modulo-27 parents. Four clean parents cannot
exhaust them. Choose the remaining fine parent there, and use
$U'=U\setminus\{\beta\}$.

Relabel the fine symbol as $\beta$, fixing all collapsed symbols,
a-digits and other unit digits. Fine-code injectivity ensures
that $\beta$ appears only in the chosen fine parent. Its actual
unit owner g cannot cover the inserted source there, since the
source keeps the old modulo-3 coordinate and that coordinate
was chosen outside g's phase. Every other unit owner remains
excluded. The grouped source therefore still supplies nonunit
ordinary owners point by point. The unused unit owner's backup
output can remain in the replacement; no extra omission is
assumed or needed.

Eight universally good pairs supply at least eight units of gain.
Retaining three top donors still decreases the number of classes
by at least five. Four distinct safe clean assignments would
therefore contradict global minimality, proving

$$
\boxed{\nu\le3.}
\tag{CD123}
$$

Use eleven universal dummy digits in the Hall argument of CD119.
A matching covering all fifteen parents would use at least four
real digits. Its failure gives

$$
|N(V)|+11<|K|\le3|V|.
\tag{CD124}
$$

Consequently a four-word V has no clean neighbor at all, or all
five words together have at most three clean neighbors. The
resulting blocked rectangle satisfies

$$
\boxed{
|T|\ge20,\ |V|=4
\quad\text{or}\quad
|T|\ge17,\ |V|=5.
}
\tag{CD125}
$$

The same injective assignment from rectangle cells to actual top
cofactors now gives at least eighty distinct nonunit cofactors m,
each dividing W and accompanied by all three actual numerical
moduli $mq^2,3mq^2,9mq^2$ in D. The five-word alternative gives
at least eighty-five. The lower companions can still occur at
different second digits and cofactor phases. The next exchange
must account for those locations jointly; this conclusion alone
does not exclude the squared-23 branch.

A complete scoped transient Lean application checks CD125 and the
eighty-cofactor conclusion from the original family assumptions
and an actual deep original. Its 168 axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`, with no errors or
`sorryAx`. The finite Hall, grouped-slot and symbol-relabeling
steps reuse existing declarations. No new retained declaration,
freeze or coverage record is introduced. The full squared-23
exclusion and unrestricted Erdős #7 remain unresolved.

### Moving lower companions gives a joint exchange obstruction

Keep the original scope of CD125: one globally count-then-modulus-sum
minimal distinct odd nonunit whole cover, actual pure moduli 3 and 9,
all original ternary heights at most two, the common coprime
factorization, q=23, and an actual original of q-height at least two.
Take the resulting pure h, five-word private projection $\Lambda$,
changed family D, and unit-digit set U. Write
$d(i)=\lfloor\rho_i/q\rfloor\bmod q$ for an original's literal
second q-digit and $C(d,u)$ for its actual top cell. The residue
$\rho_i$ is separate data from the numerical label $3^{a_i}q^2m_i$.

For a set F of four digits, which may intersect U, define the cell
condition

$$
\begin{aligned}
\operatorname{Comp}_F(d,u)\iff
\forall i\in C(d,u),\quad
&\bigl[\forall j\in D:\ a_j=0,\ m_j=m_i
      \Longrightarrow d(j)\in F\bigr]\\
&\quad\lor
\bigl[\forall j\in D:\ a_j=1,\ m_j=m_i
      \Longrightarrow d(j)\in F\bigr].
\end{aligned}
\tag{CD126}
$$

There is at most one original of each numerical row and cofactor
in D. Thus CD126 says that every top owner has at least one lower
numerical companion which is absent from D or whose digit belongs
to F. It imposes no equality of the companions' cofactor phases.

Six distinct safe digits outside F cannot be assigned six distinct
private modulo-27 parents satisfying this condition:

$$
\boxed{
\begin{gathered}
|F|=4,\quad F\subseteq\mathbb F_q,\quad
d_1,\ldots,d_6\in\mathbb F_q\setminus(U\cup F)\ \text{distinct},\\
w_1,\ldots,w_6\in\mathbb Z/27\mathbb Z\ \text{distinct},\quad
w_j\bmod9\in\Lambda\\
\Longrightarrow\quad
\neg\bigwedge_{j=1}^{6}\operatorname{Comp}_F(d_j,w_j\bmod9).
\end{gathered}
}
\tag{CD127}
$$

To prove the obstruction, suppose all six cell conditions hold.
For each nonunit cofactor assign its at most three original rows
injectively to the output labels

$$
27m,\qquad27qm,\qquad81m.
\tag{CD128}
$$

Require a short slot, one of the first two labels, for every low
owner whose digit is outside F and for every top owner in a selected
coarse cell. CD126 ensures that no cofactor group requires all three
rows to be short. The existing grouped-slot assignment therefore
applies. A low owner at a digit in F may use the 81m slot, freeing a
short slot for its numerical top companion. Each ordinary grouped
output, and each B duplicate, retains its own owner's residue modulo
that owner's cofactor; companion phases need not agree. The three
donor outputs are the separate pure outputs below. Slot injectivity
and the distinct original numerical labels give distinct outputs.

After removing the ten selected digits, at least ten safe digits
remain, including at least six of the sixteen dense digits from
CD107. Choose five disjoint pairs with dense A endpoints. Each pair
has positive gain at every private word, by CD121. The fifteen
private modulo-27 parents accommodate the six coarse parents,
five pair parents, and three further distinct parents for pure
outputs; one parent remains. The pure outputs cover two whole
parents and two children of the third. Four ordinary modulo-81
cells remain to be encoded.

The existing arbitrary-parent code applies with five pairs and
eleven collapsed parents. Its capacity check is

$$
9|\Lambda|+5=50
\le q+5+2\cdot11=50.
\tag{CD129}
$$

It avoids U, the five A symbols, and assigns the eleven distinct
B/coarse symbols to their parents. Every other used symbol uniquely
determines an active modulo-81 cell. These ordinary fine symbols
need not equal F: a low owner outside F already has a short slot,
and a fine-slot owner whose digit is unused has no source preimage.
No extra symbol-allocation hypothesis is required.

For each target in the complete deletion hole, the source preserves
its entire modulo-9W coordinate and first q-digit. A used source
owner assigned the fine slot cannot have a coarse digit: a low owner
there requires a short slot, while a top owner belongs to its chosen
cell and also requires a short slot. Hence its ordinary source digit
determines one modulo-81 cell, which the 81m output covers. Paired
parents use the existing two-digit payment, and the four pure outputs
cover their designated pieces. This covers the whole deletion hole
and leaves the original complement covered.

Five positive pair gains exceed the three retained donor costs.
The existing whole-family comparator gives a strict decrease in the
number of classes, contradicting global minimality and proving CD127.

A complete scoped transient Lean application checks CD127 from the
original family hypotheses, including the grouped assignment,
source decoding and whole-family comparison. Its axiom closures use
only the standard axioms, with no errors or `sorryAx`. It reuses the
existing finite-selection, code and replacement results; no retained
binding declaration, freeze or coverage record is introduced.

CD127 is a necessary constraint on a hypothetical cover. It does not
show that six such cells must exist. CD125 supplies numerical
companions; proving that their actual positions permit a common
exchange remains a separate obligation.

### Incidence counts do not force the joint exchange

The numerical inventory must not be substituted for the remaining
joint source condition. A finite incidence model exhibits the gap.
It has twenty digit labels, five word labels, and eighty distinct
group labels:

$$
D_0=\{0,\ldots,19\},\qquad
V_0=\{0,\ldots,4\},\qquad
M_0=D_0\times\{0,\ldots,3\}.
\tag{CD130}
$$

For every group $(d,u)$ put one top record at cell $(d,u)$ and
two lower records whose digits both equal d. Thus each digit has
exactly four occupied words, every occupied top cell has one owner,
and the eighty groups have all three row records. The fifth word
has no top record at any digit. These are incidence data, not a
family of arithmetic progressions.

For any fine set F and coarse digit $d\notin F$, an occupied cell
has both lower companions outside F. Consequently

$$
\operatorname{Comp}_F(d,u)\iff u=4
\qquad(d\notin F).
\tag{CD131}
$$

Represent each parent by a pair in $V_0\times\{0,1,2\}$. There
are only three parents above word four. Any injective assignment
to eligible parents therefore satisfies

$$
\boxed{\#\text{assigned coarse digits}\le3.}
\tag{CD132}
$$

In particular, the model has neither four clean assignments nor
the six coarse assignments required by CD127, despite its dense
four-word inventory and eighty complete row groups. A separate
scoped transient Lean check verifies the inventory, CD131 and
the parent bound, using only standard axioms. It supplies no odd
cover and no counterexample to a statement requiring whole coverage.

The stronger arithmetic control in
[Report 862](862-three-support-masked-rectangle-control.md)
already illustrates why comparable-original disjointness and
privacy alone do not repair this inference: its same-digit row
companions use different cofactor phases. That control has different
q and height parameters and is explicitly a noncover, so it is
not an instance of the present q=23 hypotheses.

The missing bridge must use the actual common private-source
fibres and their service at every second digit, or another valid
whole-family replacement. Counting more numerical companions
does not by itself establish the required simultaneous allocation.

### Component changes preserve whole owners only with current labels

Return to an actual globally count-then-modulus-sum minimal distinct
odd nonunit whole cover. Let q be prime, $W>0$ with $\gcd(W,3q)=1$
and $\gcd(3,q)=1$, and write every original numerical modulus as
$3^{a_i}q^{j_i}m_i$ with $a_i,j_i\le2$ and $m_i\mid W$.
Fix its pure original h of modulus $q^2$, and let D be all
height-two originals with h's first q-digit.
The base used here is the complete actual private-source projection

$$
K=\{(y\bmod9,y\bmod W):y\in\mathbb N\text{ is private to }h\},\qquad
C_i=K\cap F_i\quad(i\in D),
\tag{CD133}
$$

where $F_i$ is the full ternary-and-cofactor support of original i.
In particular, K is not an independently chosen rectangle or mask.
Write $t_i$ for i's literal second q-digit. A permutation $\pi_b$ at
each base point and an effective digit $\delta_i$ obey the whole-owner
invariant when

$$
\pi_b^{-1}(t_i)=\delta_i\qquad(b\in C_i).
\tag{CD134}
$$

Initially $\pi_b$ is the identity and $\delta_i=t_i$. Choose two
current effective digits a and b, form the intersection graph of
their owners' complete supports $C_i$, and choose one connected
component. Let $\tau_x$ swap a and b on the union of that component's
supports and be the identity elsewhere. Component constancy makes
this choice constant on each active owner's whole support. Owners
of other effective digits are fixed by the swap. Therefore the update

$$
\pi'_x=\pi_x\circ\tau_x,\qquad
\delta'_i=\tau_x(\delta_i)\quad(x\in C_i)
\tag{CD135}
$$

preserves CD134; for an empty support, use the same chosen-component
rule for its effective label. The graphs must use the current effective
digits, and the swap is composed on the right. Repeated left swaps
on graphs of the original digits are not the update asserted here.
Every supplied finite sequence of CD135 preserves the invariant.

For any fixed initial code $f_0$, this gives the whole-support identity

$$
\{x:b(x)\in C_i,\ \pi_{b(x)}(f_0(x))=t_i\}
=\{x:b(x)\in C_i,\ f_0(x)=\delta_i\}.
\tag{CD136}
$$

This identity alone does not assert that a fibre of an arbitrary
$f_0$ is one arithmetic progression.

### From effective digits to actual residue changes

For CD134 there is a direct arithmetic realization. Keep every
numerical modulus. Leave non-D residues unchanged, and for each
$i\in D$ choose one CRT residue satisfying

$$
\rho'_i\equiv\rho_i\pmod{9W},\qquad
\rho'_i\equiv(\rho_i\bmod q)+q\delta_i\pmod{q^2}.
\tag{CD137}
$$

The resulting family covers all integers. To see the source of this
claim, take a target in the complete deletion hole, keep its entire
modulo-9W coordinate and first q-digit, and replace its second digit
t by $\pi_{b(x)}(t)$. The exact-hole identity keeps that source in
the old hole, so an old covering owner i lies in D. Its full base
support contains $b(x)$, and CD134 forces $\delta_i=t$. Hence the
single new CRT progression for i covers the target. Outside the
hole the unchanged original complement pays. Finite periodicity
supplies integer coverage.

All numerical moduli, their distinctness, oddness and nonunit property
are unchanged. Both global minimality properties are inherited because
their comparison bounds use the same class count and modulus sum.
There is no requirement that the permutations fix the unit digits,
the donor digit, or previously selected pair symbols.

Scoped transient Lean applications check the actual whole-owner
finite-sequence specialization and this whole-integer CRT realization,
using only standard axioms. They reuse existing component, CRT,
exact-hole and finite-family results; no binding declaration is retained.
They do not produce an improving sequence. Under the earlier q=23
standing hypotheses, including the actual pure originals 3 and 9,
CD127 applies anew to the rephased family with its own witnesses;
the unit-digit set can change. Finding a legal rephasing that
violates that obstruction remains a separate existence problem.

### The exact service criterion for residue rephasing

The permutation invariant is a sufficient construction. The full
criterion can instead be stated directly on the fixed supports.
For an assignment $\delta:D\to\mathbb F_q$, define

$$
\operatorname{Service}(\delta)
\iff
\forall b\in K\ \forall t\in\mathbb F_q\quad
\exists i\in D:\ b\in F_i\ \land\ \delta_i=t.
\tag{CD138}
$$

Thus every color class of original labels must cover the same
complete K. A label receives one digit valid on its entire support;
different source points cannot choose different digits for that label.
The exact equivalence is

$$
\boxed{\operatorname{Service}(\delta)
\iff\text{there exists a whole cover with the same numerical moduli,
 the unchanged non-D residues, and the D residues prescribed by CD137}.}
\tag{CD139}
$$

For sufficiency, take a target in the old deletion hole. Its base
belongs to K. Apply CD138 to its literal second digit, and choose
the original label i supplied there. Its ternary-and-cofactor
conditions are the target's actual conditions, its first q-digit
is the common donor prefix, and its new second digit is the target's
digit. The CRT progression CD137 therefore covers the target.
The unchanged complement covers all remaining targets.

For necessity, fix one $b\in K$ and one digit t. Choose an actual
old private witness over b and use CRT to insert t while preserving
the full modulo-9W data and first q-digit. The resulting integer
belongs to the old complete deletion hole. A new covering owner
cannot be a retained non-D original. Its D residue gives second
digit t, and preservation of its modulo-9W phase gives membership
in its old support $F_i$. This is exactly CD138. This necessity
argument does not separately require preservation of every first
q-digit; the more restrictive CD137 contract supplies it for the
equivalence and the invariance below.

The criterion uses no equality constraint on the new colors of
overlapping owners that originally had the same color. It is a
cover-decomposition problem on complete actual supports, rather
than an assumption that all admissible assignments are generated
by the component moves CD135. The polychromatic terminology and
the balanced-incidence sufficient theorem are already used in
the discussion following CD39 and [Report385 Section142](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#142-balanced-depth-layers-with-stable-heavy-incidence-give-fixed-original-label-codes).
That theorem requires balancedness; no balancedness of the present
actual incidence matrix is asserted here.

### The complete private base survives a successful reset

For any actual reset satisfying the CD139 contract, form the new
coordinates from its actual residues. Then

$$
D'=D,\qquad F'_i=F_i\quad\text{for every original }i,
\qquad K'=K.
\tag{CD140}
$$

The first equality follows from the unchanged first q-digits. The
second follows by reducing the preserved modulo-9W phases to the
original ternary and cofactor moduli. Both actual deletion holes
are identical, since they delete the same index set and retain
the same other progressions. Apply the exact-hole identity to each
family: an old private witness supplies a new private witness with
the same full modulo-9W coordinate, and conversely. Their projections
are therefore equal. The private integers themselves need not be
the same, since the donor's second digit may change.

Consequently the masks $C_i$ and their actual intersections can be
reused after a reset. A different unit-digit set or different effective
labels must still be read from the new residues. Scoped transient
Lean applications verify both directions of CD139 and all three
equalities in CD140 from the stated original-family hypotheses,
with standard axiom closures and no retained binding declaration.

The remaining existence obligation is now precise: find one fixed
assignment on these complete arithmetic supports that satisfies
CD138 and creates a forbidden exchange under the earlier q=23
conditions, or find a different fully paid whole-family replacement.
These checks establish the criterion and its preservation, not such
an assignment. The q=23 exclusion, the complete height-two branch
and unrestricted Erdős #7 remain unresolved.

### Actual prime-private roots permit independent second-digit permutations

Keep the original family and coordinates of CD133–CD140, including
unrestricted count-then-modulus-sum minimality, the actual pure
$q^2$ original h, $a_i,j_i\le2$, $m_i\mid W$ and $(W,3q)=1$.
Assume an actual pure3 original g is present. Let $Q>0$ be any common
period divisible by every original modulus, and put
$r_3=\rho_g\bmod3$. Numerical divisor closure supplies the pure-p
original for every support prime. For each such original p, define

$$
V_p=\{x\bmod3:0\le x<Q,\ x\text{ is private to the original }p\},
\qquad T=(\mathbb Z/3\mathbb Z)\setminus\{r_3\}.
$$

The source condition is the original nonconcentrated-prime condition
of [Report385, Sections70–71](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#71-only-nonconcentrated-prime-support-can-supply-nonconcentrated-ancestors),
written without normalizing the pure3 phase:

$$
R=\{p>3:p\text{ is an actual support prime and }V_p=T\}
\subseteq\{q\}.
\tag{CD141}
$$

This permits $R=\varnothing$ and requires no nonconcentration of q
or its higher powers. The finite private sets retain every original
class test; they are not selected witnesses or an independently
supplied color partition.

Write $t_i=\lfloor\rho_i/q\rfloor\bmod q$ and keep the exact unit
image $U=\{t_i:i\in D,\ m_i=1\}$. There is one fixed function
$\kappa:\mathbb N\to\mathbb Z/3\mathbb Z$, depending on the original
family, such that

$$
m_i>1,\ a_i>0\quad\Longrightarrow\quad
\rho_i\equiv\kappa(m_i)\pmod3.
\tag{CD142}
$$

For EVERY family of permutations $\pi_c$ of $\mathbb F_q$, indexed
by $c\in\mathbb Z/3\mathbb Z$ and fixing U pointwise, prescribe

$$
\delta_i=
\begin{cases}
t_i,&m_i=1,\\
\pi_{\kappa(m_i)}(t_i),&m_i>1.
\end{cases}
$$

Apply this prescription only to $i\in D$. It gives an actual whole
cover with the same numerical moduli, unchanged non-D residues,
all residues preserved modulo $9W$, and all first q-digits preserved.
The new second digit of each D owner is $\delta_i$. In particular,

$$
D'=D,\qquad F'_i=F_i\ \text{for every original }i,
\qquad K'=K,\qquad U'=U.
\tag{CD143}
$$

The function $\kappa$ is chosen before the permutations and depends
only on the numerical cofactor. Thus existing same-m companions use
the same permutation, including row zero. CD142 concerns the first
ternary root of positive rows; their complete modulo9 phases are
preserved separately. Both global minimum objectives are inherited.

To derive the actual prime inputs, take any prime $p\mid m_i$.
Numerical divisor closure supplies the original pure p class, while
coprimality and oddness give $p>3$ and $p\ne q$. Irredundancy gives
it a private point, and every such point avoids the actual pure3
phase. Reduction modulo Q preserves privacy because every original
modulus divides Q; it also preserves the ternary root because $3\mid Q$.
If its complete private projection had both live roots, CD141 would
force $p=q$. It therefore has one actual private root $\alpha_p$.
These are consequences of the original R condition.

The actual concentrated-prime result supplies an original $3p$ with
ternary root $\alpha_p$ and a first-p phase used by no other original
whose modulus is divisible by p. For any finite set P of these primes
and any source x whose ternary root differs from every $\alpha_p$,
finite CRT produces y at those actual singleton phases with the same
ternary root as x. It preserves the entire modulus coordinate of every
original containing no prime of P. Every P-bearing original misses y:
its p-phase would force it
to be the corresponding $3p$ original, whose ternary root is wrong.
No abstract pruning hypothesis enters this reset.

Applying this reset to a private point also shows that every private
point of a p-bearing original has root $\alpha_p$: otherwise all
P-bearing classes are removed and all remaining class tests stay
false, contradicting whole coverage. One may take
$\kappa(m)=\alpha_{\min\operatorname{PrimeDiv}(m)}$ for occurring
$m>1$. An original private point then proves CD142.

For the complete Service argument, fix $b\in K$ and a target digit t.
Choose an actual h-private witness w over b, put $c=w\bmod3$, and
insert $\pi_c^{-1}(t)$ as its second q-digit while preserving its
entire modulo-$9W$ coordinate. The exact prefix-liability identity
places this source x in the full retained-family hole. Reset the
finite set of actual cofactor primes with $\alpha_p\ne c$.
Every retained class still misses the resulting y: it is either
removed by the reset or has its whole original modulus coordinate
preserved from x. Original whole coverage supplies an owner i in D.
It contains no reset prime, so the SAME whole-modulus preservation
transfers its membership back from y to x. Hence $b\in F_i$ and
$t_i=\pi_c^{-1}(t)$. If $m_i>1$, its selected cofactor prime has
$\alpha_p=c$, giving $\delta_i=t$. If $m_i=1$, then $t_i\in U$ and
pointwise fixation of U gives the same conclusion. This proves CD138
on the complete K, without a product decomposition or an assumed
Service certificate. CD139 supplies the actual residue realization;
CD140 and the fixed unit digits give CD143.

A scoped transient Lean application verifies this theorem from the
finite-period R premise, including divisor closure, private-point
reduction, the actual singleton/reset construction, Service and all
stated invariances. It reuses the frozen prime-prefix liability
result and pinned Mathlib CRT and finite-family results; its axiom
closures contain only `propext`, `Classical.choice` and `Quot.sound`.
No retained mathematical declaration or new originality claim is made.
Among D owners with the same numerical cofactor, these permutations
preserve equality of second digits.
They do not force six payable cells, a strict exchange, or exclusion
of $q=23$; those existence obligations remain unresolved.

### Root-local fine sets share the same six-request obstruction

Keep the actual family and finite-period condition CD141, now with
q=23 and actual pure originals 3 and 9. Thus every original has
ternary and q-height at most two, the cofactors divide one positive
W coprime to 3q, and h is the actual pure $q^2$ original. Both
minimality conditions are over all distinct odd nonunit whole covers.
Use the literal unit-digit image U, the complete h-private modulo9
projection $\Lambda$, and the cell predicate CD126.

For each ternary root c choose four distinct safe fine digits,
allowing a different set at each root:

$$
F_c\subseteq\mathbb F_{23}\setminus U,\qquad |F_c|=4
\quad(c\in\mathbb Z/3\mathbb Z).
\tag{CD144}
$$

There cannot be six requests $(d_j,w_j)$ with all the following
properties:

$$
\boxed{
\begin{gathered}
w_1,\ldots,w_6\in\mathbb Z/27\mathbb Z\text{ are distinct},
\qquad w_j\bmod9\in\Lambda,\\
d_j\notin U\cup F_{w_j\bmod3},\\
w_j\equiv w_k\pmod3\ \land\ d_j=d_k\ \Longrightarrow\ j=k,\\
\operatorname{Comp}_{F_{w_j\bmod3}}(d_j,w_j\bmod9)
\quad\text{for every }j.
\end{gathered}
}
\tag{CD145}
$$

Digits may coincide across different ternary roots. The fine sets
need not agree across roots. Each cell condition still quantifies
over every actual top owner in that cell, including all numerical
cofactors and their actual lower companions in D.

To prove the obstruction, choose ten distinct digits outside U:
four common fine targets and six globally distinct request targets.
This is possible because the exact unit image has at most three
digits. At each root, the four local fine digits, the request digits
at that root, and U form disjoint sets. Map them respectively to the
four common fine targets, their designated request targets, and
themselves. The same-root distinctness in CD145 makes this map
injective. Finite permutation extension supplies one permutation
at each root fixing U pointwise. CD141–CD143 realize all these
permutations in one actual whole cover.

The cell conditions transfer to that cover on their full supports.
Indeed, take any new top owner at a designated request target.
Its digit lies outside the new unit image, so its cofactor is
nonunit. Its preserved modulo9 phase and CD142 identify its
cofactor color with the request's root. Inverting that root's
permutation places it in the old requested cell. Any row-zero or
row-one companion with the same numerical cofactor uses the same
permutation, so the old cell condition puts its new digit among
the four common fine targets. This handles every new top owner;
it does not select one favorable owner per cell.

The complete private-base equality CD143 transfers each requested
parent's private witness to the new family. Apply the existing
q=23 density result afresh to this actual family. Its pure $q^2$
original is h by distinctness of numerical moduli. If that result
returns a unit-digit superset, reduce it to the literal unit image:
the safe dense-digit set only grows. CD127 now applies to the four
common fine targets and six globally distinct request targets,
contradicting minimality.

A complete scoped transient Lean application checks this implication
from the original whole-cover hypotheses and the literal finite-period
R condition, including all-owner cell transport, private-base
transport, and the new family's density and exact unit image.
Its axiom closure contains only `propext`, `Classical.choice` and
`Quot.sound`. The application reuses the earlier exchange and
rephasing constructions; no new retained Lean declaration, freeze
or coverage record is introduced.

CD145 removes the need to align fine sets or request digits between
ternary roots before testing the obstruction. It does not supply
six requests. In particular, equal second digits of D owners with
the same numerical cofactor remain equal under CD142's common
permutation. The required actual incidence or alternative exchange,
the q=23 exclusion and unrestricted Erdős #7 remain unresolved.

### A same-root protected digit can be removed from safe-top companions

Keep the original whole-cover hypotheses of CD144–CD145, including
q=23 and CD141. Suppose the unit original $g$ of modulus $9q^2$
belongs to D, and its first ternary root agrees with that of the
pure9 original z. Write

$$
c=\rho_g\bmod3=\rho_z\bmod3,\qquad
\gamma=\lfloor\rho_g/q\rfloor\bmod q\in U.
\tag{CD146}
$$

There is an actual whole-cover representative with the same numerical
modulus at every index, the same non-D and unit-D residues, the same
first q-digits, and the same complete K and exact U, such that

$$
\boxed{
\begin{gathered}
i\in D,\quad a_i=2,\quad t_i\notin U,\quad
\rho_i\bmod3=c,\\
j\in D,\quad a_j\le1,\quad m_j=m_i
\quad\Longrightarrow\quad t_j\ne\gamma.
\end{gathered}
}
\tag{CD147}
$$

Here all residues and digits in CD147 are read in the new representative.
Both global minimum objectives are retained. Its finite-period private
root set still satisfies $R\subseteq\{q\}$; equality with the old R
is not asserted. The individual full supports may change.

For the construction, retain each actual cofactor-prime singleton
guard of modulus 3p from CD141's proof. Its literal first-p phase
is used by no other p-bearing original. Consider all actual whole
covers with the fixed data above that preserve these guards, and
minimize the number of row-two D owners whose second digit is outside U.
The original family supplies a candidate, so well-ordering of the
attained natural counts gives a minimum. No third minimum is assumed
of the original family.

Fixed singleton guards recover the complete private-root constraint
in every candidate. At a private point in the wrong ternary root,
reset p to its guard phase while preserving the whole modulus of
every p-free original. All p-bearing originals then miss the new
point, as do all p-free originals, contradicting coverage. This
argument uses the candidate's actual cover; it does not assume its
private-root classification was preserved.

Suppose the minimum candidate violates CD147 with top i and low j.
Their common cofactor is nonunit. The preceding private-root law
places every private point of j at root c. Such a point avoids
the pure9 word and the unit $9q^2$ word: its full q-square phase
already agrees with that unit. These two modulo9 words are different,
since otherwise the unit class would be contained in pure9. Only
one word over c remains. Hence all private points of j agree
modulo $9q^2m_i$.

Apply the comparable private-hull exchange of
[Report385, Section176](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#176-reciprocal-private-hull-swaps-leave-one-exact-joint-liability).
Give the low numerical label a private point of i as residue, and
the top numerical label a private point of j. The new low class
covers the entire old top class; the new top covers every old
private point of j. Comparable old classes are disjoint, so every
remaining target has an unchanged owner. Thus the replacement
preserves whole coverage with the same numerical labels.

The two changed labels have the same cofactor. At each prime
dividing their common cofactor, the new phases exchange the two old
phases, both avoiding the fixed singleton phase. At every other
cofactor prime, both changed labels are prime-free and every
prime-bearing label is unchanged.
Both changed labels stay in the same first-q parent, and neither is
a unit. The swap is therefore another candidate. The top digit
changes from outside U to gamma, while the changed low row is not
counted. The minimized count strictly falls, a contradiction.

Equality of K follows from the unchanged D and non-D complement,
then the exact-hole identity applied to both actual families.
It does not follow from unchanged owner supports. The fixed singleton
guards give concentrated private roots for every cofactor prime in
the new family, which proves its finite-period $R\subseteq\{q\}$.

A complete scoped transient Lean application verifies the actual
representative construction, including the singleton-root argument,
whole private-hull swap, candidate invariants and attained-count
minimum. Its checked axiom closures contain only `propext`,
`Classical.choice` and `Quot.sound`. No retained Lean declaration,
freeze or coverage record is introduced.

The conclusion removes this protected-digit alternative in one
representative and in the specified root. If the unit $9q^2$ root
differs from the pure9 root, two private words can remain, so this
argument no longer guarantees a single-class payment. Equal safe digits
within a cofactor group are also unaffected: swapping two equal digits does
not lower the count. CD147 supplies no six-request existence or
q=23 exclusion.

## Full prime guards exclude the q=23 branch at ternary height two

For this section, fix one actual finite cover with pairwise distinct
odd numerical moduli greater than one, globally minimum in class
count and then in modulus sum among all such whole covers. The
comparison class is unrestricted: competing covers need not preserve
ternary height, prime support, or residue normal form. Assume actual
pure3 and pure9 classes and write every original numerical label as

$$
 d_i=3^{a_i}23^{e_i}m_i,
 \qquad 0\le a_i\le2,\quad e_i\ge0,
 \qquad m_i\mid W,\quad W>0,\quad (W,69)=1.
$$

Choose a positive common period Q for all original moduli. Let
$P_i(Q)$ be the complete private set of original i in $\mathbb Z/Q$,
and let $c_3$ be the actual pure3 root. Define the literal set

$$
 R_Q=\left\{p>3:\ p\text{ prime, an original }g_p\text{ has }d_{g_p}=p,
 \quad\pi_3(P_{g_p}(Q))=\mathbb F_3\setminus\{c_3\}\right\}.
$$

The following conclusion uses $R_Q\subseteq\{23\}$, not equality.
It allows 23 to be absent from the actual prime support. All
nonternary prime heights are arbitrary finite heights.

**CD148.** Under these conditions, no such whole cover exists.
No actual $9\cdot23^2$ unit, protected-nine normal form, aligned
unit phases, private-hull equality, or six-request lower bound is
an additional premise.

Every actual support prime $p\ne3,23$ occurs in an actual cofactor.
The finite-period singleton implication supplies one fixed actual
class of modulus $3p$ whose first-p phase occurs in no other
p-bearing original. Its ternary root is live. Choose these
singletons once for the whole original family. They give a single
partition of all non23 support primes between the two roots
$c_9,c_*$ outside $c_3$, where $c_9$ is the actual pure9 root.
The pure9 root is live because otherwise pure9 would be contained
in pure3.

The complete private region of the actual pure-p class lies in
its singleton's root. At $c_9$ it can occupy at most two modulo9
words; at $c_*$ it can occupy at most three. Apply the actual
whole-cover terminal-donor descent SC440 with these complete
private projections. Use the actual finite maximum
$M=\max_i e_i$ and auxiliary common period $9\cdot23^M W$;
no uniform bound on M is assumed. For $p>27$, descent occurs whenever
$27k+1\le p+9$, with $k=2$ or $3$. Global count/sum minimality
therefore gives

$$
 p\le43\quad\text{at }c_9,
 \qquad p\le71\quad\text{at }c_*.
 \tag{CD149}
$$

These are consequences of the same actual family and the fixed
singleton choices. No stronger SC442 threshold is used.

### One full product law on each root

Fix either live root c. On every opposite-root prime axis, fix the
complete prime-power word at its actual singleton phase. This
excludes every original bearing that prime, including row-zero
originals. On every remaining axis p, including 23 when present,
condition the uniform full prime-power word on avoiding every
actual pure $p^h$ phase and every actual $3p^h$ phase, for all
positive depths. The latter guards are imposed regardless of their
ternary root. Missing numerical labels may receive dummy forbidden
prefixes; these only impose extra restrictions.

If $H_p$ is the actual maximum depth, put

$$
 \sigma_p=\sum_{h=1}^{H_p}p^{-h},
 \qquad \rho_p=\Pr(\text{both full guard families are avoided}),
 \qquad b_p=\frac{\sigma_p}{\rho_p}.
$$

The union bound on that one axis gives
$\rho_p\ge1-2\sigma_p>0$. A positive-depth literal prefix has
conditional mass at most $p^{-h}/\rho_p$; depth zero has mass
exactly one. Thus

$$
 0\le b_p\le\frac1{p-3},
 \qquad b_{23}\le\frac1{20}.
$$

For the ternary coordinate, retain uniformly the two modulo9 words
over $c_9$ outside pure9, or all three over $c_*$. Take the product
of this law and the full prime-axis laws. CRT turns every product
point into one integer tested against the unchanged original
moduli and residues. Original whole coverage is therefore coverage
of this same probability space.

Let $P_c=\prod_p(1+b_p)$ and $B_c=\sum_p b_p$, over the active
nonternary axes. Every numerical label has at most one owner.
In rows zero and one, all zero-support and single-prime-support
labels have zero probability: they are nonunit-excluded, pure3,
one of the imposed actual guards, or excluded by an opposite-root
fixed axis. In row two, the zero-support label is pure9 and also has probability zero. Summing the remaining
original event bounds by their actual exponent vectors gives

$$
 1\le2(P_c-1-B_c)+\kappa_c(P_c-1),
 \qquad \kappa_{c_9}=\frac12,
 \quad\kappa_{c_*}=\frac13.
 \tag{CD150}
$$

The subtraction here removes exact numerical slots before bounding
the sum. It does not subtract unrelated upper estimates. Inactive
positive-depth coordinates contribute zero only through exclusion
of actual original events; a matching prefix under a fixed-point
law need not itself have zero probability.

### The two necessary budgets are incompatible

Set

$$
 S=\{5,7,11,13,17,19,29,31,37,41,43\},
 \qquad T=\{47,53,59,61,67,71\}.
$$

For any finite $B\subseteq S\cup T$, define

$$
 E_\kappa(B)
 =(2+\kappa)\left[
   \left(1+\frac1{20}\right)
   \prod_{p\in B}\left(1+\frac1{p-3}\right)-1\right]
 -2\left[\frac1{20}+\sum_{p\in B}\frac1{p-3}\right].
$$

The load in CD150 is coordinatewise nondecreasing for nonnegative
weights: $P_c-1-B_c$ is the sum of all product monomials of degree
at least two, and $P_c-1$ contains all positive degrees. Consequently
one may increase weights to their displayed caps and pad absent
primes, including an absent 23. Take A to be the actual non23
primes at $c_9$. By CD149, $A\subseteq S$ and the other root's
non23 primes are contained in $(S\setminus A)\cup T$. Both roots
would therefore require

$$
 E_{1/2}(A)\ge1,
 \qquad E_{1/3}((S\setminus A)\cup T)\ge1.
$$

Exact rational comparison over the $2^{11}$ subsets proves

$$
 \forall A\subseteq S,\qquad
 E_{1/2}(A)<1\ \text{or}\
 E_{1/3}((S\setminus A)\cup T)<1.
 \tag{CD151}
$$

This contradicts the two necessary budgets and proves CD148.
The finite comparison is checked directly by Lean's kernel; the
full scoped transient application also derives the singleton
palette, actual product events, guarded zero slots, exponent-vector
injection and both necessary budgets from the stated original-family
hypotheses. Its axiom closure contains only `propext`,
`Classical.choice` and `Quot.sound`. This is an exact application
check, not a new frozen declaration or atom-coverage claim.

CD148 excludes the specified q=23 branch of a globally extremal
cover. It does not establish that every hypothetical odd distinct
cover reduces to this branch. Other exceptional-prime sets, larger
ternary height, and unrestricted odd distinct covering remain
unresolved. The exclusion allows arbitrary finite 23-height.

## Separate actual label pools exclude a single exceptional seven

Replace 23 by 7 in the original-family conditions of CD148: the
same globally count-minimal, then same-count modulus-sum-minimal odd
distinct nonunit whole cover has actual pure3 and pure9, every
original modulus has the form

$$
 d_i=3^{a_i}7^{e_i}m_i,\qquad a_i\le2,\quad m_i\mid W,
 \qquad W>0,\quad\gcd(W,21)=1,
$$

and the complete private-root set in a positive common period Q
satisfies $R_Q\subseteq\{7\}$. Minimality still ranges over all odd
distinct nonunit whole covers; competitors are not restricted to
this displayed coordinate system. The prime 7 may be absent, and
all nonternary heights are arbitrary finite heights.

**CD152.** No whole cover satisfies these conditions.

The singleton construction and complete pure-prime donor descent
used in CD149 apply to every actual prime other than 3 and 7.
Choose the singleton owners once. Put

$$
 S_7=\{5,11,13,17,19,23,29,31,37,41,43\},
 \qquad T=\{47,53,59,61,67,71\}.
$$

If A is the set of ordinary primes whose fixed 3p singleton
owners lie in the pure9 root c, then
$A\subseteq S_7$, and the other root d uses primes from
$(S_7\setminus A)\cup T$. The 43/71 bounds count complete private
modulo9 words of the actual pure-p donor, not of its 3p singleton.
The coarser bound $b_7\le1/4$ on both roots does not by itself
exclude every partition. The additional restriction below is on
two separate inventories of the same actual numerical labels.

### Root-specific guards and two separate shared inventories

Suppose 7 occurs, and let H be its actual finite maximum height.
For each live root r define

$$
 \begin{aligned}
 \sigma&=\sum_{h=1}^{H}7^{-h},\\
 \tau_r&=\sum_{\substack{1\le h\le H:\
     \text{an actual }3\cdot7^h\text{ class has root }r}}7^{-h},\\
 \eta_r&=\sum_{\substack{1\le h\le H:\
     \text{an actual }9\cdot7^h\text{ class has root }r}}7^{-h},\\
 t_r&=6\tau_r,\qquad v_r=6\eta_r.
 \end{aligned}
 \tag{CD153}
$$

Each numerical label $3\cdot7^h$ or $9\cdot7^h$ has at most
one original owner, and any such owner lies in one ternary root.
The two roots therefore satisfy

$$
 t_c,t_d,v_c,v_d\ge0,\qquad
 t_c+t_d\le1,\qquad v_c+v_d\le1.
 \tag{CD154}
$$

There is no claim that the 3-tower and 9-tower root assignments
coincide. They are different inventories constrained separately.

On root r, keep the ordinary-axis law of CD150, including the
fixed opposite-root singleton coordinates. On the 7-axis, condition
on avoiding all actual pure $7^h$ prefixes and only the actual
$3\cdot7^h$ prefixes whose ternary root is r. Absent pure labels
may be padded with forbidden prefixes. No absent 3-tower label is
counted in $\tau_r$. If $\rho_r$ is this guard-survival probability,
then

$$
 \rho_r\ge1-\sigma-\tau_r>0,\qquad
 b_{7,r}=\frac{\sigma}{\rho_r}\le\frac1{5-t_r},\qquad
 \frac{\eta_r}{\rho_r}\le\frac{v_r}{5-t_r}.
 \tag{CD155}
$$

These estimates use $6\sigma\le1$. They keep the same conditional
law in the prefix bounds, the event inventory and the shared
high-label contribution.

For the ordinary active weights $b_p$, let

$$
 P_r=\prod_p(1+b_p),\qquad B_r=\sum_p b_p,
 \qquad C_r=(2+\kappa_r)(P_r-1),\qquad
 \beta_r=C_r-2B_r,
$$

where $\kappa_c=1/2$ and $\kappa_d=1/3$. The exact numerical-slot
sum before applying CD155 is

$$
 \beta_r+C_r b_{7,r}+\kappa_r\frac{\eta_r}{\rho_r}.
$$

Rows zero and one have no surviving single-prime slots. In row
two, a shared-only slot contributes only when its actual
$9\cdot7^h$ owner has root r. Opposite-root owners have zero event
probability. Every remaining label is counted once by its original
exponent vector. Since $C_r\ge0$, whole coverage forces

$$
 1\le \beta_r+\frac{C_r+\kappa_r v_r}{5-t_r}.
 \tag{CD156}
$$

In the absent-7 case the ordinary inventory gives the same
necessary upper envelope with $t_r=v_r=0$: its added nonnegative
term only weakens that necessary condition. No fictitious 7-owner
or allocation is asserted.

### A finite certificate excludes every coupled allocation

For $B\subseteq S_7\cup T$ and $\kappa\in\{1/2,1/3\}$, put

$$
 \begin{aligned}
 P(B)&=\prod_{p\in B}\left(1+\frac1{p-3}\right),\qquad
 B_1(B)=\sum_{p\in B}\frac1{p-3},\\
 C_\kappa(B)&=(2+\kappa)(P(B)-1),\qquad
 \beta_\kappa(B)=C_\kappa(B)-2B_1(B),\\
 E_\kappa(B;t,v)&=\beta_\kappa(B)+
          \frac{C_\kappa(B)+\kappa v}{5-t},\\
 D_\kappa(B;t)&=
          \frac{(1-\beta_\kappa(B))(5-t)-C_\kappa(B)}{\kappa}.
 \end{aligned}
 \tag{CD157}
$$

Coordinatewise monotonicity allows ordinary weights to increase
to $1/(p-3)$ and missing ordinary primes to be padded. For
$0\le t,v\le1$, the coarse envelope is

$$
 E_\kappa(B;t,v)\le
 \beta_\kappa(B)+\frac{C_\kappa(B)+\kappa}{4}.
$$

An exact rational comparison over all $2^{11}$ choices
$A\subseteq S_7$, with $A'=(S_7\setminus A)\cup T$, proves that
either one root's coarse envelope is below one, or both

$$
 \begin{aligned}
 D_{1/2}(A;0)+D_{1/3}(A';1)&>1,\\
 D_{1/2}(A;1)+D_{1/3}(A';0)&>1.
 \end{aligned}
 \tag{CD158}
$$

In the second case, increase $t_d$ to $1-t_c$ in its envelope.
This is safe because its numerator is nonnegative. The two
necessary budgets imply

$$
 v_c\ge D_{1/2}(A;t_c),\qquad
 v_d\ge D_{1/3}(A';1-t_c).
$$

Their sum is affine in $t_c\in[0,1]$ and is greater than one at
both endpoints by CD158. This contradicts $v_c+v_d\le1$.
The argument does not assume $\beta_r\le1$ and does not infer
monotonicity from a possibly negative demand slope. This proves
CD152.

The scoped transient Lean application checks CD152 from the full
original-family hypotheses, including the absent-7 branch. Its
finite comparison is evaluated by the kernel, and the final
axiom closure contains only `propext`, `Classical.choice` and
`Quot.sound`. This supplies an exact application check, not a new
frozen declaration or atom-coverage result. The single exceptional
5 case, multiple exceptional primes and higher ternary height
remain outside CD152.

## Every single exceptional prime at least eleven is excluded

Keep one globally count-minimal, then same-count modulus-sum-minimal
odd distinct nonunit whole cover, with actual pure3 and pure9.
Let q be any prime at least eleven. Suppose the literal original
moduli satisfy

$$
 d_i=3^{a_i}q^{e_i}m_i,\qquad a_i\le2,\quad m_i\mid W,
 \qquad W>0,\quad\gcd(W,3q)=1,
$$

and, in a positive common period Q, the complete private-root set
satisfies $R_Q\subseteq\{q\}$. All nonternary heights are arbitrary
finite heights, and q is not required to occur. The competing covers
in the two minimality conditions are unrestricted odd distinct
nonunit whole covers.

**CD159.** No whole cover satisfies these conditions.

Use the construction of CD148–CD150 with q in place of 23.
For every actual prime other than 3 and q, choose its fixed actual
3p singleton. The complete private modulo9 projection of the actual
pure-p donor yields the same bounds 43 at the pure9 root and 71 at
the other root. Put

$$
 \begin{aligned}
 S&=\{5,7,11,13,17,19,23,29,31,37,41,43\},\\
 T&=\{47,53,59,61,67,71\},\\
 S_q&=S\setminus\{q\},\qquad T_q=T\setminus\{q\}.
 \end{aligned}
$$

Let A be the actual ordinary primes whose chosen singleton owners
have the pure9 root. Then $A\subseteq S_q$, and the other root's
ordinary primes belong to $(S_q\setminus A)\cup T_q$. Each root
uses its own full product law with opposite-root singleton
coordinates fixed. All actual pure $p^h$ and $3p^h$ prefixes on
active axes are guarded, at every height. The shared axis has
$b_q\le1/(q-3)$, and the same estimate holds on each ordinary axis
with its own p. No separate shared-tower allocation is needed in
this range of q.

For $\kappa\in\{1/2,1/3\}$ and $B\subseteq S_q\cup T_q$, define

$$
 E_{q,\kappa}(B)
 =(2+\kappa)\left[
 \left(1+\frac1{q-3}\right)
 \prod_{p\in B}\left(1+\frac1{p-3}\right)-1\right]
 -2\left[\frac1{q-3}+\sum_{p\in B}\frac1{p-3}\right].
 \tag{CD160}
$$

The exact original-label inventory and monotone padding used in
CD150 imply both necessary inequalities

$$
 1\le E_{q,1/2}(A),\qquad
 1\le E_{q,1/3}((S_q\setminus A)\cup T_q).
 \tag{CD161}
$$

Padding may include an absent q. It enlarges a nonnegative inventory
bound; it does not create an original class. Erasing q from the
ordinary palettes avoids counting the same prime twice.

For prime $11\le q\le71$, exact rational comparison proves

$$
 \forall A\subseteq S_q,\qquad
 E_{q,1/2}(A)<1\quad\text{or}\quad
 E_{q,1/3}((S_q\setminus A)\cup T_q)<1.
 \tag{CD162}
$$

The q=23 case is CD151. The remaining small-palette primes
$11,13,17,19,29,31,37,41,43$ each have $2^{11}$ partitions;
the six tail primes each have $2^{12}$ partitions.

For q at least 73, it is outside both ordinary palettes and
$1/(q-3)\le1/70$. Coordinatewise monotonicity in the shared
weight allows the uniform replacement $1/(q-3)\mapsto1/70$.
A further exact comparison over the $2^{12}$ subsets of S gives
CD162 for this entire unbounded prime range. Thus the finite
comparisons, together with the monotonicity argument, contradict
CD161 for every prime q at least eleven, proving CD159.

The scoped transient Lean application verifies the complete
original-family implication, including the finite-prime cases,
the uniform large-prime comparison, the actual source laws and
label injection. Its final axiom closure contains only `propext`,
`Classical.choice` and `Quot.sound`. The kernel finite comparisons
cover 47,104 cases in addition to CD151's 2,048 q=23 cases.
This is an exact application check, not a new frozen declaration
or atom-coverage claim.

Together CD152 and CD159 exclude every single-exception hypothesis
$R_Q\subseteq\{q\}$ for prime $q\ge7$ under their displayed source
conditions. They give no exclusion of the single exceptional 5
case, multiple exceptional primes, greater ternary height or
unrestricted odd distinct covers. In particular, no reduction of
every hypothetical odd cover to this source class is assumed.

## Three axial high labels exclude the shared-five palette {7,11}

Fix one globally count-minimal, then same-count modulus-sum-minimal
finite odd distinct nonunit whole cover F. Assume actual pure3 and
pure9, ternary height at most two, and the complete private-root set
$R_Q=\{5\}$ in the actual least common period Q. At the root c of
the actual pure9 original, suppose the ordinary concentrated prime
palette is exactly $\{7,11\}$. All other prime heights are arbitrary
finite heights. The competing covers in both minimality conditions
remain unrestricted.

**CD163.** No whole cover satisfies these conditions.

The proof retains the actual residues and uses the literal
opposite-root singleton elimination of CD148–CD150. The key
additional constraint is the joint union of the three numerical
labels 45, 63 and 99. They cannot independently occupy the same
safe modulo9 word at their separate maximal capacities.

For each $p\in\{5,7,11\}$, remove from the uniform coordinate
$\mathbb Z/p^{v_p(Q)}\mathbb Z$ every prefix of an actual pure
$p^a$ original and every prefix of an actual $3p^a$ original at c.
Let $Z_p$ be the complement and $\rho_p$ its ambient density.
Only actual guards at their actual roots are removed. Each tower
has total measure at most $\sum_{a\ge1}p^{-a}$, so

$$
 \rho_p\ge\frac{p-3}{p-1}>0,\qquad
 \rho_5\ge\frac12,\quad
 \rho_7\ge\frac23,\quad
 \rho_{11}\ge\frac45.
 \tag{CD164}
$$

Choose the three coordinates independently and uniformly on their
respective $Z_p$. Choose independently one of the two complete
modulo9 words above c that avoid the actual pure9 residue. Fix
the opposite-color prime coordinates at their established singleton
values. Denote this one product law by $\mu$. Every sample is an
actual CRT point and is covered by an original of F. After literal
opposite-color elimination, each event of positive measure has
numerical modulus $3^j5^e7^a11^b$, with $0\le j\le2$.

For positive exponents use the coordinate bounds

$$
 f_5(e)=2\,5^{-e},\qquad
 f_7(a)=\frac32\,7^{-a},\qquad
 f_{11}(b)=\frac54\,11^{-b},
 \quad f_p(0)=1.
 \tag{CD165}
$$

Their positive-exponent sums are respectively $1/2,1/4,1/8$.
They bound each actual prefix under the same chosen law;
they are not assertions that any event attains its bound.

Let $L_0$ be the complete actual five-free low union, consisting
of the surviving row-zero and row-one events. The single-axis
low events were removed by the actual guards. Every remaining
member of $L_0$ uses both 7 and 11, and $L_0$ depends only on
those ordinary coordinates. With $\ell=\mu(L_0)$ and
$W=(1+1/4)(1+1/8)-1=13/32$, numerical distinctness gives

$$
 0\le\ell\le\frac1{16},\qquad
 \mu(L_5)\le W,\qquad
 \sum_{\substack{e,a,b\ge0\\a+b\ge1}}
       \frac12 f_5(e)f_7(a)f_{11}(b)
       =\frac{39}{128}.
 \tag{CD166}
$$

Here $L_5$ is the remaining actual low union. Set
$U=(L_0\cup L_5)^c$, the complement of the complete low union.
Every point of U must be covered by a high event. For the unit
high label $9\cdot5^e$, independence from $L_0$ and CD164 yield

$$
 \mu(A_{9\cdot5^e}\cap U)
 \le5^{-e}(1-\ell).
 \tag{CD167}
$$

Consequently the individual45 allowance is $(1-\ell)/5$,
and all other unit high labels together have allowance at most
$(1-\ell)/20$. An absent or inactive label contributes zero.
The infinite geometric sums merely enlarge the finite numerical
inventory; each actual numerical label is counted once.
Whole coverage now implies

$$
 \begin{aligned}
 1&\le\ell+W+\frac{39}{128}
          +\frac{1-\ell}{5}+\frac{1-\ell}{20}\\
  &=\frac{123}{128}+\frac34\ell
   \le\frac{129}{128}.
 \end{aligned}
 \tag{CD168}
$$

If45 has zero contribution, its omission saves at least
$(1-\ell)/5\ge3/16>1/128$, contradicting CD168.
The ordinary-bearing high inventory contains one63 allowance
$3/28$ and one99 allowance $5/88$. Omitting either also saves
more than $1/128$. Thus all three labels actually occur and
have positive selected measure. Each must occupy one of the
two safe complete words above c. This argument derives their
existence and root ownership from the inventory itself.

Let $x_5,x_7,x_{11}$ be their actual first-prime cylinder
probabilities. Then

$$
 0<x_5\le\frac25,\qquad
 0<x_7\le\frac3{14},\qquad
 0<x_{11}\le\frac5{44}.
 \tag{CD169}
$$

If two of these labels use the same safe word, their complete
union on $\mu$ has probability
$(x_p+x_q-x_px_q)/2$. This equality uses independence on the
complete product law before intersection with U. No independence
conditioned on U is assumed. Since $x+y-xy$ is increasing on
$[0,1]^2$, replace the two individual allowances in CD168 by
this joint bound and retain every other allowance unchanged.
The guaranteed decreases are

$$
 \begin{array}{c|c}
 \text{equal-word pair}&\text{decrease in the same inventory}\\\hline
 63,99&15/1232\\
 45,63&3/70-\ell/5\ge17/560\\
 45,99&1/44-\ell/5\ge9/880.
 \end{array}
 \tag{CD170}
$$

The $\ell/5$ terms pay for replacing the old45 allowance on
$L_0^c$ by a complete-union allowance. The other unit labels
retain their separate bound on U. Thus this replacement never
subtracts an alleged actual loss from an unknown event measure.

Three labels on two safe words contain an equal-word pair.
Every decrease in CD170 exceeds $1/128$; even the weakest gives

$$
 1\le\frac{129}{128}-\frac9{880}
   =\frac{7023}{7040}<1.
 \tag{CD171}
$$

This contradiction proves CD163. The proof does not require a
positive selected measure for the private25 source, a GLC collision
graph, any new exchange operation, or saturation of the inventory.
A complete scoped transient Lean application verifies CD163 directly
from the original whole cover and the displayed source conditions.
It constructs the cofactor coordinates and the guarded product law,
derives the clipped covering inequality and all three positive actual
label owners, and combines the equal-word pair with the joint union
bound. The endpoint takes neither a supplied coordinate frame nor a
scalar covering inequality as a premise. Both minimality conditions
range over all odd distinct nonunit integer covers; the private-root
set is measured on the original family's exact least common period,
and the ordinary palette uses its actual $3p$ singleton owners.
The check compiles without warnings; its final axiom closure contains
only `propext`, `Classical.choice` and `Quot.sound`. This is a transient
exact check, not a retained declaration, freeze or atom-coverage claim.

CD163 excludes precisely the displayed shared-five palette. Other
ordinary palettes for shared five, multiple exceptional primes,
higher ternary height and unrestricted odd distinct covering remain
unresolved.

## Whole axial towers and the remaining joint-realization gap

Keep the same globally count-then-modulus-sum minimal hypothetical
cover, actual 3 and 9, ternary height two, and shared-prime set
$R_Q=\{5\}$. Allow an arbitrary ordinary palette $A$ at a live root.
Use one root-selective product law, and let $k=2$ at the pure-nine
root and $k=3$ at the other live root. All original numerical labels
and their residues remain fixed.

For ordinary primes put

$$
 g_p=\frac1{p-3},\quad
 W=\prod_{p\in A}(1+g_p)-1,\quad
 B=\sum_{p\in A}g_p,\quad D=W-B,\quad
 L=2D,\quad P=\prod_{p\in A}(1-g_p).
 \tag{CD172}
$$

Let $L_0$ be the complete five-free low union under this law and
$\ell=\mu(L_0)$. The ordinary low inventory gives $\ell\le L$.
This event depends only on ordinary coordinates. With the actual
shared-five depth masses $\sigma,\tau,\eta$, choose upper caps
$b\ge\sigma/\rho$ and $r\ge\eta/\rho$, with $0\le b,r\le1/2$,
where $\rho$ is the surviving shared-coordinate density.
The previous bounds retain
low five-bearing allowance $2bW$ and nonsingle-axis high allowance
$((1+b)W-B)/k$.

For each safe complete ternary word $j$, take the coordinate union
of all actual high labels $9p^a$ assigned to that word, including
all positive finite depths. Its coordinate mass is $x_{p,j}$.
Define $x_{5,j}$ in the same way for the shared-five unit tower.
Unique original labels and the geometric bounds imply

$$
 x_{p,j}\ge0,\quad \sum_jx_{p,j}\le g_p,\qquad
 x_{5,j}\ge0,\quad \sum_jx_{5,j}\le r.
 \tag{CD173}
$$

Missing labels contribute zero. On each word the ordinary axial
union has probability $1-\prod_p(1-x_{p,j})$ on the complete
product law. The five coordinate is independent of the whole
ordinary event $L_0$. Consequently the union of all axial high
labels, intersected with the complete low complement, is at most
$G_\ell(x)/k$, where

$$
 G_\ell(x)=\sum_j\left[
 x_{5,j}(1-\ell)+(1-x_{5,j})
 \left(1-\prod_{p\in A}(1-x_{p,j})\right)\right].
 \tag{CD174}
$$

This uses independence before conditioning on the low complement.
It does not assert independence on that complement.

Define the finite partition quantity

$$
 M_k(s)=\min_{f:A\to\{0,\ldots,k-1\}}
 \left[(1-s)\prod_{f(p)=0}(1-g_p)
       +\sum_{j=1}^{k-1}\prod_{f(p)=j}(1-g_p)\right].
 \tag{CD175}
$$

Empty products are one. The expression in CD174 is affine in each
axis vector separately. Each vector lies in the simplex specified
by CD173, so successive maximization sends every vector to a vertex.
The ordinary-axis coefficients are nonnegative. The shared-axis
coefficient at word $j$ is $\prod_p(1-x_{p,j})-\ell$, which is
nonnegative if $\ell\le P$. Under an established upper bound
$\ell\le\bar L\le P$, all axis caps may therefore be used at
vertices of this relaxation, giving

$$
 G_\ell(x)\le k-M_k(r)-r\ell.
 \tag{CD176}
$$

This optimization bounds the response of one fixed actual source.
It does not reassign the residues or word ownership of that source.
Keeping every other numerical allowance once, and using $k-r>0$
to replace $\ell$ by $\bar L$, whole coverage implies

$$
 M_k(r)\le(k-r)\bar L+(2k+1)bW+D.
 \tag{CD177}
$$

The left side is a minimum over assignments. A particular assignment
satisfying this inequality certifies feasibility of the relaxed
criterion; the inequality is not required for every assignment.
No simultaneous attainability of the remaining allowances follows.

### Reusing independence to sharpen the low allowance

For a fixed disjoint split $A=S\sqcup T$, write
$L_S=2(\prod_{p\in S}(1+g_p)-1-\sum_{p\in S}g_p)$ and similarly
for $T$. The actual low subfamilies supported wholly inside these
two blocks depend on disjoint ordinary coordinate sets. If their
masses are $x,y$, their union has mass $x+y-xy$. When $L_S,L_T\le1$,
monotonicity on $[0,1]^2$ bounds it by $L_S+L_T-L_SL_T$.
All cross-block low slots retain their old allowances. Thus

$$
 \ell\le\bar L=L-L_SL_T.
 \tag{CD178}
$$

This is the existing independent-union formula applied to two
complete subfamilies in the same inventory. It subtracts no alleged
actual intersection from an unknown total. The full $L_0$ still
includes the cross-block labels.

### A finite shared-label allocation survives these inequalities

The joint criterion remains feasible even with unique finite
ownership of the shared labels. Take

$$
 \begin{aligned}
 A_c&=\{7,17,23,37\},\\
 A_d&=\{11,13,19,29,31,41,43,47,53,59,61,67,71\}.
 \end{aligned}
 \tag{CD179}
$$

At shared height four, assign the low unit labels 15 and 75 to $c$,
and 375 and 1875 to $d$. Assign high unit label 45 to $c$, and
225, 1125 and 5625 to $d$. This assigns each listed numerical label
once; it is not a construction of the rest of a covering family.
Normalize each mass by four. Then

$$
 \begin{aligned}
 u&=4\sum_{e=1}^4 5^{-e}=\frac{624}{625},\\
 (t_c,t_d)&=\left(\frac{24}{25},\frac{24}{625}\right),&
 (v_c,v_d)&=\left(\frac45,\frac{124}{625}\right),\\
 b_i&=\frac{u}{4-u-t_i},& r_i&=\frac{v_i}{4-u-t_i},\\
 (b_c,b_d)&=\left(\frac{156}{319},\frac{156}{463}\right),&
 (r_c,r_d)&=\left(\frac{125}{319},\frac{31}{463}\right).
 \end{aligned}
 \tag{CD180}
$$

These are finite-height caps, obtained from
$\rho_i\ge1-\sigma-\tau_i$; neither shared pool is replaced by its
infinite-height limit. For the high-axis assignments in CD175,
put the shared-five axis at word zero on each root. At $c$, put
all ordinary axes at word one. At $d$, use the three groups
$\{19,29,59\}$, $\{13,31,41,43,67\}$ and
$\{11,47,53,61,71\}$ in word order.

For CD178 choose $S_c=\{7,17\}$ and $T_c=\{23,37\}$; choose
$S_d=\{11,13,19,71\}$ and $T_d=A_d\setminus S_d$. Both block
caps are at most one and $0\le\bar L_i\le L_i\le P_i$.
The low corrections $L_SL_T$ are $1/9520$ at $c$ and
$569764945282797/200211880214528000$ at $d$.
Direct exact evaluation of the displayed assignments gives the
following positive differences between the right side of CD177
and the particular assignment's left side:

$$
 \begin{aligned}
 \Delta_c&=\frac{250233}{6073760}>0,\\
 \Delta_d&=\frac{65201864993954333721}{4078716423730364416000}>0.
 \end{aligned}
 \tag{CD181}
$$

Since $M_k$ is no larger than a particular assignment's value,
these inequalities establish feasibility of this capacity model.
They do not provide actual ordinary prefixes or realize the low,
axial-high and mixed-high allowances jointly. The same finite
shared-label ownership survives the whole-tower and the displayed
disjoint-low-block improvements, so these inequalities alone cannot
exclude every remaining palette. Further progress requires additional
constraints on their common actual realization, or a different
necessary criterion.

A transient Lean check verifies the finite shared-label pools, the
stated disjoint partitions, the two low-block corrections, their
admissible bounds and both feasibility inequalities for these explicit
word assignments. It uses only the standard axioms. The general
actual-source derivation of CD173–CD178 is the ordinary argument above;
this finite check does not formalize that entire implication.

### Literal divisor-parent constraints do not force a mixed-packet loss

Numerical divisor closure and disjointness of comparable original
classes preserve useful source information, but do not alone force a
positive loss in a packet

\[
 \{5p,15p,45p,9p,45\}.                               \tag{CD182}
\]

An explicit finite control uses all eleven nonunit divisors of315.
The actual residues and private witnesses modulo315 are:

| Modulus | Residue | Private witness |
| --- | --- | --- |
|3|0|3|
|5|0|5|
|7|0|7|
|9|1|19|
|15|1|31|
|21|1|43|
|35|24|59|
|45|22|67|
|63|16|79|
|105|73|178|
|315|193|193|

Every displayed private witness lies in its own class and no other.
For every two distinct labels with $m\mid n$, the actual residues obey

\[
 a_n\not\equiv a_m\pmod m.                         \tag{CD183}
\]

Thus the comparable classes are disjoint. The family does not cover:
the integer2 is outside every class.

Use the single uniform law on the thirty CRT cells

\[
 (z,u,v)\in\{4,7\}\times\{2,3,4\}
                    \times\{2,3,4,5,6\},            \tag{CD184}
\]

where $z=x\bmod9$, $u=x\bmod5$ and $v=x\bmod7$. These are exactly
the two safe words above ternary root1 and the complements of the
actual pure/root guards at5 and7. On this same source:

| Actual class | Event in $(z,u,v)$ | Probability |
| --- | --- | --- |
|45|$(4,2,*)$|$1/6$|
|63|$(7,*,2)$|$1/10$|
|35|$(*,4,3)$|$1/15$|
|105|$(*,3,3)$|$1/15$|
|315|$(4,3,4)$|$1/30$|

All five events are pairwise disjoint. Each attains its finite
first-depth slot cap, so their actual union has probability

\[
 \frac16+\frac1{10}+\frac1{15}+\frac1{15}+\frac1{30}
       =\frac{13}{30}.                              \tag{CD185}
\]

In particular the mixed35/105/315 union attains the sum of its three
slot allowances, even with the literal proper-parent inequalities
and the unique numerical ownership retained. No universal strictly
positive debit follows from these local conditions alone.

This control has five-height1 and no25 label. It neither satisfies
whole-cover extremality nor tests a conclusion that actually uses
complete-private25 supply. It also makes no claim of saturating
infinite-height caps. It specializes the existing local-compatibility
controls of Report385 §§47,173,175 to the precise five-label packet.

A transient exact Lean check verifies all eleven labels and private
witnesses, the complete nonunit divisor inventory, comparable-class
disjointness, the thirty conditioned points, each of the five event
counts and their disjoint union. Its three checked endpoints use only
the permitted standard axioms. This verifies the finite control, not
a source transport or a whole-cover exclusion.

### The complete-private25 supply still needs a source transport

Report385 §174 gives a sourcewise lower bound $187/2500$ on the
complete simultaneous-deletion hole, using its own fibre law for
each $y\in Y$. Its supplier condition at ternary height2 includes75
and225. Hence a supplier described as mixed with5 need not contain
an ordinary prime. The lower bound alone does not force service
from one of the ordinary-prime packets CD182.

For a supplier that does contain an ordinary prime, numerical
divisor closure does not copy its phase to the actual parent.
Indeed CD183 requires a different reduced phase for every proper
comparable parent. Projecting deep or multi-prime suppliers to a
first-depth numerical label can also merge many distinct originals.
A proposed charging map must retain those phase differences, all
supplier rows and depths, and its full congestion.

Finally, the literal private25 region is contained in the actual25
class. The selected guarded law excludes that class along with the
other pure-five guards, and therefore assigns the literal private
region zero mass. A statement on the complete private fibre cannot
be inserted as a positive-mass statement on that selected law.
A useful bridge must explicitly transport complete deletion-hole
service, with its actual source coordinates and weights, or build a
repair of the entire deletion hole. These source conditions are
not supplied by the local packet inequalities.

## Complete mixed-five deletion supplies the guarded source

Keep one globally count-minimal, then same-count modulus-sum-minimal
odd distinct nonunit whole cover, actual pure3 and pure9, ternary
height at most two, and shared-prime set $R_Q=\{5\}$ in its actual
least common period. The competing covers in both minimality
conditions remain unrestricted. Assume $G=v_5(Q)\ge2$, and write

$$
 Q=5^G N,\qquad N=9M,\qquad \gcd(M,15)=1,
 \qquad n=3^{h_n}5^{e_n}m_n,
 \quad 0\le h_n\le2,\quad\gcd(m_n,15)=1.
$$

Every numerical label $n$ and residue $a_n$ below belongs to this
one original family $D$. Here ordinary-bearing means $m_n>1$.
Divisor closure supplies the original25. Put
$\beta=a_{25}\bmod25$ and $\omega=\beta\bmod5$.

Reuse [Report385, Q2P1](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#174-every-complete-private-source-of-q2-demands-a-fixed-mixed-service).
Let $Y\subseteq\mathbb Z/N$ be the complete survivor of all
five-free originals after removing the cofactor cylinders of every
actual $e_n=1$ original whose first-five phase is $\omega$. Then
$Y\ne\varnothing$ and
$\operatorname{Priv}_{25}=\operatorname{CRT}(Y\times[\beta]_{25})$.
No selected private witnesses replace this complete set.

### The complete deletion retains every unit supplier

Delete precisely

$$
 \mathcal M=\{n\in D:e_n\ge1,\ m_n>1\},\qquad
 E_{\mathcal M}=(\mathbb Z/Q)\setminus
                     \bigcup_{n\notin\mathcal M}A_n.
$$

All unit originals $5^e,3\cdot5^e,9\cdot5^e$ remain, including75
and225. This deletion family differs from Q2P2's narrower $J$;
the following lower bound is for $E_{\mathcal M}$.

For every $y\in Y$, use the complete fibre
$B_\omega=\{t\bmod5^G:t\equiv\omega\pmod5\}$ and define

$$
 E_y=\{t\in B_\omega:(y,t)\in E_{\mathcal M}\},\qquad
 d(y)=\frac{|E_y|}{5^{G-1}},\qquad
 C_n=\{y\bmod N:y\equiv a_n\pmod{n/5^{e_n}}\}.
$$

The fixed deep ordinary supplier family is
$\mathcal T=\{n\in D:e_n\ge2,\ m_n>1,\ a_n\equiv\omega\pmod5\}$.
Then

$$
 \begin{aligned}
 d(y)&\ge d_G:=\frac14+\frac34\,5^{1-G}>\frac14,\\
 \sum_{n\in\mathcal T}5^{1-e_n}\mathbf1_{C_n}(y)&\ge d(y).
 \end{aligned}
 \tag{CD186}
$$

Indeed every five-free original and every first-five-depth original
misses this fibre by the definition of $Y$. The retained possible
owners are therefore the three unit labels at each depth
$2\le e\le G$. Each has relative fibre mass at most $5^{1-e}$,
and numerical distinctness permits each label once. Their union
has mass at most $3\sum_{e=2}^G5^{1-e}=1-d_G$.
Whole coverage supplies the second inequality. Since one deep
ordinary trace has relative mass at most $1/5<d_G$, at least two
distinct actual members of $\mathcal T$ meet $E_y$. No shallow
parent, ordinary depth or cofactor-phase agreement is inferred.

### Singleton reset makes the complete hole compatible with the law

Fix a live root $i$. Write its existing law as
$\mu_i=\nu_i\otimes U_{Z_{5,i}}$, where $\nu_i$ includes the
uniform safe full modulo9 word, all active ordinary coordinates
on their actual guard complements, and the fixed opposite-root
singleton coordinates. Put $\rho_i=|Z_{5,i}|/5^G$.

The reset $\pi_i$ changes only those opposite-root coordinates to
the singleton words already fixed by $\nu_i$. The actual3p
singleton is the only p-bearing original at its first-p phase;
it misses at root $i$, and every other p-bearing original misses
after the reset. All other original events retain their phases.
Thus the reset preserves private25 membership. The active guards
and the pure3/pure9 guards already miss every private25 point.
This is the projection/lift argument of
[Report385, TC2](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#138-singleton-root-pruning-improves-the-two-root-original-source-budget),
applied to the same complete shallow-safe source:

$$
 \pi_i(Y_i)\subseteq Y_i\cap\operatorname{supp}\nu_i,
 \qquad Y_i=\{y\in Y:y\bmod3=i\}.
$$

Consequently every root with $Y_i\ne\varnothing$ has
$\theta_i:=\nu_i(Y)>0$, and at least one such root exists.
On this support every removed five guard is a retained unit
original at the same root, so $E_y\subseteq Z_{5,i}$.
For $E=\{(y,t):y\in Y,\ t\in E_y\}$, finite counting gives

$$
 \begin{aligned}
 \mu_i(E)&=\frac1{5\rho_i}\int_Y d(y)\,d\nu_i(y)
             \ge\frac{d_G\theta_i}{5\rho_i}>0,\\
 \sum_{n\in\mathcal T}\mu_i(A_n\cap E)&\ge\mu_i(E).
 \end{aligned}
 \tag{CD187}
$$

The safe-word weight is already in $\nu_i$; there is no additional
$1/k$ in CD187. Literal private25 still has zero $\mu_i$-mass,
because the actual25 guard removes it. CD187 concerns the complete
mixed-deletion hole above its cofactor source.

The complete source also admits an explicitly priced transport.
Let $\varpi=(\pi_i)_*U_{Y_i}$, retaining every reset multiplicity,
and condition uniformly on the whole $E_y$ above each resulting
$y$. The resulting law $\psi$ has marginal $\varpi$ and satisfies

$$
 \frac{d\psi}{d\mu_i}(y,t)
   =\frac{5\rho_i\varpi(y)}{\nu_i(y)d(y)}\mathbf1_{E_y}(t),
 \qquad
 C_\varpi=5\rho_i\max_{\varpi(y)>0}
                     \frac{\varpi(y)}{\nu_i(y)d(y)}.
$$

The price $\psi\le C_\varpi\mu_i$ is exact for this marginal
and these fibres: the target capacity over $y$ is
$\nu_i(y)d(y)/(5\rho_i)$, and uniform conditioning attains the
required ratio. No height-independent price follows. Conditional
normalization and the one-law cylinder calculation are reused
from [Report572, FS2–FS3a](../550-599/572-compatible-fibres-lift-one-six-prime-query-law.md#1-a-compatible-fibre-lift-preserves-the-pure-q-query-contribution)
and [Report385, CF3–CF5](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#124-complete-cofactor-fibres-refine-the-actual-joint-liability-charge).
The source-specific input here is CD186 together with the reset
support, rather than a new general coupling theorem.

### The actual45 pays for the source word it removes

Fix a root with $\nu(Y)>0$ and suppress its index. Write
$\nu=U_J\otimes\lambda$, where $J$ is its set of $k\in\{2,3\}$
safe full modulo9 words and $\lambda$ is its ordinary product
law. Retain CD172's $b,r,W,D,P$ and $\ell\le\bar L\le P$;
here $r$ is the shared-axis cap.

For $j\in J$, let $A_j$ be the actual ordinary axial high union,
and let $B_j^0$ be the actual five-free nonaxial high union.
Both are events on the same ordinary carrier. Define

$$
 \begin{aligned}
 P_j&=\prod_p(1-x_{p,j}),\qquad
 a'_j=\lambda(A_j\setminus L_0),\\
 c_j&=\lambda(L_0^c\cap A_j^c),\qquad
 q_j=\lambda(L_0^c\cap A_j^c\cap(B_j^0)^c),\\
 b_j^0&=\lambda(B_j^0),\qquad
 \zeta_0=\nu(R_5)=\frac1k\sum_jq_j.
 \end{aligned}
 \tag{CD188}
$$

Here $R_5$ is the complete survivor of all five-free originals.
The active single-axis low originals were already guarded, so
this decomposition retains every remaining five-free event.
In particular $a'_j+c_j=1-\ell$ and $q_j\le c_j$.

The actual5 has first-five phase different from $\omega$, by
comparable-original disjointness with25. An actual15 at this
root with first-five phase $\omega$ would kill all of $Y$ there.
Thus the first-five-depth unit-cofactor exclusion $U_1$ removes
at most the word of actual45. Put $\chi=1$ if45 has first-five
phase $\omega$ and a safe word $j_0$ here; otherwise put $\chi=0$.
Let $I=J\setminus\{j_0\}$ when $\chi=1$, and $I=J$ otherwise.
Then $\nu(R_5\setminus U_1)=\zeta_0-\chi q_{j_0}/k$.

Put

$$
 \gamma=\frac{|Z_5\cap B_\omega|}{|Z_5|},\qquad
 s=\frac1{5\rho}-\gamma\ge\frac1{25\rho}>0.
$$

The inequality uses the entire actual25 prefix removed from
$B_\omega$. If $\chi=1$, the actual45 coordinate mass is
$\gamma$, whereas its old numerical slot is $1/(5\rho)$.
Every other unit slot keeps its old allowance. Thus, for the
actual high-unit vectors of CD173,
$\sum_jx_{5,j}+s\le r$.
Increase only $x_{5,j_0}$ by $s$ to obtain a vector $z_5$
in that same simplex. Keep all ordinary vectors unchanged.

The exact axial-high union on $L_0^c$ has mass
$k^{-1}\sum_j(a'_j+x_{5,j}c_j)$. Its increase at $z_5$ is
exactly $sc_{j_0}/k$. Applying CD174–CD176 to $z_5$ therefore
bounds the axial-high contribution on the complete low complement by

$$
 \frac{k-M_k(r)-r\ell-\chi s c_{j_0}}{k}.
 \tag{CD189}
$$

This uses one actual45 slot and its actual coefficient $c_{j_0}$.
The alternative cap replacement $r\mapsto r-s$ describes the
same loss and cannot be added as a second debit.

Let $\mathcal H$ be the actual $e_n=1$, ordinary-bearing family
at first-five phase $\omega$. For each of its original slots,
independence gives $\mu(A_n)=\gamma\nu(C_n)$, whereas its
uncorrected slot is at least $\nu(C_n)/(5\rho)$. Hence these
slots lose $s\sum_{n\in\mathcal H}\nu(C_n)$.
They belong to the five-bearing low or nonaxial-high inventory;
none belongs to $L_0$, CD178's correction or the axial tower.

The exact source identity
$Y=(R_5\setminus U_1)\setminus\bigcup_{n\in\mathcal H}C_n$
and $q_{j_0}\le c_{j_0}$ now give

$$
 \begin{aligned}
 \operatorname{Loss}_{\rm total}
   &:=s\sum_{n\in\mathcal H}\nu(C_n)
                          +\frac{\chi s c_{j_0}}k
     \ge s[\zeta_0-\nu(Y)]_+,\\
 M_k(r)+ks[\zeta_0-\Theta]_+
   &\le(k-r)\bar L+(2k+1)bW+D
       \qquad\text{whenever }\Theta\ge\nu(Y).
 \end{aligned}
 \tag{CD190}
$$

Thus the unit slot pays for the whole source word it removes.
No original label is charged twice, and no alleged intersection
is subtracted from an unknown union measure.

### Wordwise inventories retain the same unit and supplier ownership

The five-free nonaxial inventory gives $\sum_jb_j^0\le D$.
Consequently

$$
 \zeta_0\ge\frac1k\sum_j[P_j-\bar L-b_j^0]_+
          \ge\frac{[M_k(0)-k\bar L-D]_+}{k}.
 \tag{CD191}
$$

For $j\in I$, the exact $d(y)$ depends only on the complete
modulo9 word; denote it by $d_j$. Let $g$ be the relative
$B_\omega$ mass removed by the pure-five and root-specific
$3\cdot5^e$ guards. Let $u_j$ be the relative mass of the deep
$9\cdot5^e$ union at $j$ remaining after those guards. Then

$$
 s=\frac{g}{5\rho},\qquad g\ge\frac15,\qquad
 d_j=1-g-u_j\ge d_G.
$$

The same numerical high-unit label has one word owner, so the
$d_j$ are not independently chosen minima.

Let $C_n^{\rm ord}$ retain the literal ordinary cylinder after
singleton elimination. Inactive ternary or opposite-root events
contribute zero. Define

$$
 \begin{aligned}
 L_{\rm deep}
   &=\sum_{\substack{n\in\mathcal T\\h_n\le1}}
           5^{1-e_n}\lambda(C_n^{\rm ord}),\\
 H_{{\rm deep},j}
   &=\sum_{\substack{n\in\mathcal T\\h_n=2,\ \operatorname{word}(n)=j}}
           5^{1-e_n}\lambda(C_n^{\rm ord}),\qquad
 a_G=\frac{1-5^{1-G}}4.
 \end{aligned}
$$

A low original supplies one fixed column across all words; a high
original has one actual word. CD186 on the same slices $Y_j$
gives

$$
 \begin{aligned}
 \nu(Y)&\le\mathsf T:={1\over k}\sum_{j\in I}{1\over d_j}
       \int_{Y_j}\sum_{\substack{n\in\mathcal T\\n\text{ active at }j}}
             5^{1-e_n}\mathbf1_{C_n^{\rm ord}}\,d\lambda\\
 &\le\Theta_{\rm word}:={1\over k}\sum_{j\in I}
                      {L_{\rm deep}+H_{{\rm deep},j}\over d_j},\\
 L_{\rm deep}&\le2a_GW,\qquad
 \sum_jH_{{\rm deep},j}\le a_GW.
 \end{aligned}
 \tag{CD192}
$$

The latter inequalities use the existing prefix caps and each
original numerical slot once. Exact finite inventories may
replace $W$ term by term. The deep slots bound demand above;
they are not also subtracted from the covering budget.

In particular CD190 implies

$$
 \begin{aligned}
 M_k(r)+s[\Phi]_+&\le(k-r)\bar L+(2k+1)bW+D,\\
 \Phi&=\sum_j[P_j-\bar L-b_j^0]_+
                 -\sum_{j\in I}{L_{\rm deep}+H_{{\rm deep},j}\over d_j}.
 \end{aligned}
 \tag{CD193}
$$

A weaker independent-inventory lower substitute for $\Phi$ is

$$
 M_k(0)-k\bar L-D-a_GW
          \left(2\sum_{j\in I}{1\over d_j}
                         +\max_{j\in I}{1\over d_j}\right).
$$

Replacing every $d_j$ by $d_G$ weakens it further. None of these
positive parts is asserted to be uniformly positive.

### Second-five colors impose a common allocation

At $j\in I$, the active depth-two unit labels25,75,225 occupy
distinct second-five digits, by comparable-original disjointness.
Let $\mathcal C_j$ be the unoccupied digits above $\omega$.
Its size is four minus the indicator of an active75 at this
root and first phase, minus the indicator of an active225 at
this word and first phase. Thus it has two, three or four digits;
the75 indicator is common to the root and the225 indicator is
nonzero at at most one word.

For $c\in\mathcal C_j$, let $\delta_{j,c}$ be the exact residual
unit-hole density on its complete second-five fibre. Only the
three unit towers at depths $e\ge3$ can remain there. Hence

$$
 \delta_{j,c}\ge h_G:=\frac14+\frac34\,5^{2-G}>\frac14.
 \tag{CD194}
$$

At $G=2$ this density is one. Every such color requires actual
mixed deep service at each source point. This is the complete
sibling-fibre argument with the retained unit inventory; it does
not select a favorable tail or infer common phases for different
originals.

Partition the same actual $\mathcal T$ labels by their fixed
second-five color. Define $L_c,H_{j,c}$ as in CD192, retaining
only that color and replacing $5^{1-e_n}$ by $5^{2-e_n}$.
With $A_G=5a_G$, the common columns satisfy

$$
 \begin{aligned}
 \lambda(Y_j)&\le\min_{c\in\mathcal C_j}
                       {L_c+H_{j,c}\over\delta_{j,c}},\\
 \sum_cL_c&\le2A_GW,\qquad
 \sum_{j,c}H_{j,c}\le A_GW.
 \end{aligned}
 \tag{CD195}
$$

The average of these minima is a valid $\Theta$ in CD190.
It bounds $\nu(Y)$ directly, not necessarily $\mathsf T$.
Each low original has one color across all words, and each high
original has one pair $(j,c)$; separate favorable allocations at
different words are not allowed.

More explicitly, take any nonnegative weights $w_{j,c}$ with
$\sum_{c\in\mathcal C_j}\delta_{j,c}w_{j,c}\ge1$ for every
$j\in I$, and set weights outside these pairs to zero.
Multiplying the same color demands gives

$$
 \begin{aligned}
 \sum_{j\in I}\lambda(Y_j)
 &\le\sum_c\left(\sum_jw_{j,c}\right)L_c
                         +\sum_{j,c}w_{j,c}H_{j,c}\\
 &\le A_GW\left(2\max_c\sum_jw_{j,c}
                              +\max_{j,c}w_{j,c}\right).
 \end{aligned}
 \tag{CD196}
$$

This finite weighted inequality retains the same source and
actual supplier colors. It is not a fractional repair certificate
from integer minimality.

### The remaining source inequality

Let
$S=(k-r)\bar L+(2k+1)bW+D-M_k(r)$ be the old CD177 slack.
For $S\ge0$, one sufficient closing condition is

$$
 \sum_jq_j-
   \sum_{j\in I}\frac1{d_j}
      \int_{Y_j}\sum_{\substack{n\in\mathcal T\\n\text{ active at }j}}
         5^{1-e_n}\mathbf1_{C_n^{\rm ord}}\,d\lambda
       >\frac{S}{s}.
 \tag{CD197}
$$

CD195 or CD196 can replace the second sum by another certified
upper bound for $k\nu(Y)$. Every quantity must concern the same
$q_j,Y_j$, unit residuals, original phases and shared low columns.
CD186–CD196 do not force CD197 for every permitted original
source. The unresolved step is a quantitative restriction on that
common realization; positive transport mass alone supplies no
such inequality or whole-hole repair.

A scoped transient Lean application verifies CD186 for the entire
five-free projection of the actual25 private region: the complete
mixed-deletion fibre bound, its actual deep-supplier bound, and two
distinct original suppliers meeting the hole. It uses only the
standard axioms and requires neither minimality hypothesis for this
conditional fibre implication. It does not assert source nonemptiness
or verify the selected-law reset. This is reuse evidence, with no new
frozen declaration. The selected-law transport, debit and word/color
inventory bounds CD187–CD197 remain ordinary mathematical derivations
and are not claimed as formalized. No unrestricted Erdős #7 conclusion
follows.

## Deep excess and the actual45 payment share one covering budget

Keep the same original family and selected law as CD186–CD197,
with $\nu(Y)>0$. The deletion hole remains the complete
$E_{\mathcal M}$ for
$\mathcal M=\{n\in D:e_n\ge1,\ m_n>1\}$; it is not the
narrower Q2P deletion hole. Retain all the original phases,
the safe-word measure in $\nu$, and the same $\mu$.

Write

$$
 q(y)=\sum_{n\in\mathcal T}5^{1-e_n}\mathbf1_{C_n}(y),
 \qquad
 S=(k-r)\bar L+(2k+1)bW+D-M_k(r).
$$

CD186 gives $q\ge d$ on $Y$. The excess $q-d$ counts raw deep
capacity beyond the complete hole's demand. Both capacity spent
on retained originals and multiplicity inside the hole can be
paid from the original budget.

### An exact majorant keeps the sources of loss disjoint

Let $V_5$ be the union of all actual high unit-five events
$9\cdot5^e$, and let $V_o$ be the union of the actual ordinary
axial events $9p^a$. Let $\mathcal I_{\rm ind}$ consist of the
remaining individually counted originals: mixed-five low labels
and nonaxial high labels. This is a budget classification, not a
new deleted family. In particular
$\mathcal H\cup\mathcal T\subseteq\mathcal I_{\rm ind}$ and
$\mathcal H\cap\mathcal T=\varnothing$.

Use the actual-cofactor raw allowances

$$
 u_n=
 \begin{cases}
  5^{-e_n}\nu(C_n)/\rho,&e_n\ge1,\\
  \nu(C_n),&e_n=0.
 \end{cases}
$$

They satisfy $u_n\ge\mu(A_n)$ and are no larger than their
existing coordinate-product slots. Hence
$\sum_{n\in\mathcal I_{\rm ind}}u_n
 \le2bW+(bW+D)/k$.
On the support of the same $\mu$, define

$$
 F=\mathbf1_{L_0}
   +\sum_{n\in\mathcal I_{\rm ind}}\mathbf1_{A_n}
   +\mathbf1_{L_0^c}
       \bigl(\mathbf1_{V_5}
                +(1-\mathbf1_{V_5})\mathbf1_{V_o}\bigr).
 \tag{CD198}
$$

Every original of positive selected measure belongs to one of
these groups. Whole coverage therefore gives $F\ge1$.
The axial term is the exact axial union restricted to $L_0^c$;
its expectation is
$k^{-1}\sum_j(a'_j+x_{5,j}c_j)$, using CD188's actual coefficients.
Put

$$
 \mathcal B=\ell+\sum_{n\in\mathcal I_{\rm ind}}u_n
                +\frac1k\sum_j(a'_j+x_{5,j}c_j).
$$

Finite expectation gives the exact decomposition and the old
axis-envelope upper bound

$$
 \begin{aligned}
 \mathcal B-1
   &=\sum_{n\in\mathcal I_{\rm ind}}
                  \bigl(u_n-\mu(A_n)\bigr)
                      +\int(F-1)\,d\mu,\\
 \mathcal B-1+\frac{\chi s c_{j_0}}k&\le\frac Sk.
 \end{aligned}
 \tag{CD199}
$$

Every term in the first line is nonnegative. For the second
line, add $s$ to the same actual45 coordinate when $\chi=1$.
The resulting $z_5$ satisfies the original total cap $r$, and

$$
 \sum_j(a'_j+x_{5,j}c_j)+\chi s c_{j_0}
   =\sum_j(a'_j+z_{5,j}c_j)
   \le G_\ell(z_5)\le k-M_k(r)-r\ell.
$$

Combine this with the individual raw-slot bound and
$\ell\le\bar L$. This is the same actual45 payment as CD189;
no second $r\mapsto r-s$ deduction is made.

### Raw deep losses and surviving overcount combine exactly

For $n\in\mathcal H$, its raw-slot loss is exactly
$s\nu(C_n)$. Now restrict the pointwise overcount to

$$
 \mathscr F=Y\times(Z_5\cap B_\omega).
$$

On this set all five-free and all first-five-depth originals
are absent. The only individually counted events are those in
$\mathcal T$, and the only retained owners still possible are
the high unit-five events. Thus, pointwise on $\mathscr F$,

$$
 F-1=\sum_{n\in\mathcal T}\mathbf1_{A_n}
                       -\mathbf1_{E_{\mathcal M}}.
$$

For each $n\in\mathcal T$, its raw-slot loss restricted to
cofactors in $Y$ is
$5^{-e_n}\nu(Y\cap C_n)/\rho-\mu(A_n\cap\mathscr F)$.
It is nonnegative, as is its complementary raw-slot loss.
Adding these restricted losses to the integral of the preceding
identity cancels the actual deep event masses and leaves exactly
$(5\rho)^{-1}\int_Y(q-d)\,d\nu$.

The shallow and deep label sets are disjoint. Their chosen
losses, the nonnegative overcount on $\mathscr F$, and the
actual45 axis payment therefore give

$$
 \begin{aligned}
 \mathfrak D_*&:=
      s\sum_{n\in\mathcal H}\nu(C_n)
       +\frac{\chi s c_{j_0}}k
       +\frac1{5\rho}\int_Y(q-d)\,d\nu,\\
 0\le\mathfrak D_*&\le\frac Sk.
 \end{aligned}
 \tag{CD200}
$$

The deep integral pays for both overlapping surviving deep events
and raw deep prefixes removed by retained guards. These charges
are obtained from CD199's exact decomposition, not by subtracting
an alleged overlap from an unknown event union.

### Deep charge must stay close to the complete five-free source

Let $a=\nu(Y)$, $t=\mathsf T$ from CD192, and
$\zeta_0=\nu(R_5)$. Then $a\le\min\{\zeta_0,t\}$.
The first two terms of $\mathfrak D_*$ are at least
$s(\zeta_0-a)$ by CD190. The last is at least
$d_G(t-a)/(5\rho)$. Eliminating $a$ gives

$$
 \begin{aligned}
 \mathfrak D_*&\ge
       s[\zeta_0-t]_++\frac{d_G}{5\rho}[t-\zeta_0]_+,\\
 \zeta_0-\frac{S}{ks}
       &\le t\le\zeta_0+\frac{5\rho S}{kd_G}
                        \qquad(S\ge0).
 \end{aligned}
 \tag{CD201}
$$

Thus making the deep charge large also consumes budget. These
are two bounds on the same deficit; they are not extra losses
to add to CD200.

The same argument prevents cancellation between safe words.
Put $\zeta_{0,j}=q_j/k$ and
$t_j=k^{-1}\int_{Y_j}q/d_j\,d\lambda$ for $j\in I$; set
$t_j=0$ at the word removed by45. On that removed word take
$\widehat d_j=d_G$ solely as a coefficient convention; its actual
hole is empty. Elsewhere put $\widehat d_j=d_j$. Then

$$
 S\ge k\sum_{j\in J}\left(
      s[\zeta_{0,j}-t_j]_+
          +\frac{\widehat d_j}{5\rho}[t_j-\zeta_{0,j}]_+
                         \right).
 \tag{CD202}
$$

At the removed word the second positive part is zero, and the
first is paid by $s c_{j_0}/k\ge s q_{j_0}/k$.

### A certificate on the whole five-free survivor

For every $y\in R_5$, extend the literal fibre notation by
$E_y=\{t\in B_\omega:(y,t)\in E_{\mathcal M}\}$.
This is the same complete deletion hole, including the empty
fibres at a first-depth unit owner. For $n\in\mathcal T$, put
$P_n=[a_n]_{5^{e_n}}\subseteq\mathbb Z/5^G$ and
$V_{\mathcal T}(y)=\bigcup_{n\in\mathcal T,\,y\in C_n}P_n$.
Define

$$
 \mathcal O(y)=
 \frac{\displaystyle
       \sum_{n\in\mathcal T}\mathbf1_{C_n}(y)|P_n|
                        -|E_y\cap V_{\mathcal T}(y)|}{|Z_5|}.
 \tag{CD203}
$$

This is nonnegative. On $Y$, whole coverage gives
$E_y\subseteq V_{\mathcal T}(y)$, so
$\mathcal O(y)=(q(y)-d(y))/(5\rho)$.
On $(R_5\setminus U_1)\setminus Y$, at least one actual
$\mathcal H$ cofactor cylinder is present and its shallow loss
pays $s$. The remaining part $R_5\cap U_1$ is the actual45
word; its mass times $s$ is paid by $\chi s c_{j_0}/k$.
Consequently

$$
 \int_{R_5}\min\{s,\mathcal O(y)\}\,d\nu(y)
       \le\mathfrak D_*\le\frac Sk.
 \tag{CD204}
$$

Unlike CD197, this necessary certificate does not contain the
shallow ordinary deletion mask $Y$. The deep family and its
phases remain actual originals; no replacement congruences or
new source law have been introduced.

To see its finite meaning, let
$m(y,v)=\sum_{n\in\mathcal T}\mathbf1_{C_n}(y)\mathbf1_{P_n}(v)$.
The numerator of CD203 is

$$
 \sum_{v\in B_\omega}
       \bigl(m(y,v)-\mathbf1_{E_y\cap V_{\mathcal T}(y)}(v)\bigr).
$$

Inside the reached part of the hole it counts multiplicity minus
one. Outside the hole it counts all raw deep capacity, including
prefixes outside $Z_5$. Those prefix cardinalities account for
unused original allowances; they are not probabilities under an
unrelated favorable law.

### One original matching certifies part of the paid excess

Choose one fixed matching $\mathcal P$ of original numerical
labels in $\mathcal T$. Each label occurs in at most one pair.
Require every pair $\{n,m\}$ to have compatible full prefixes,

$$
 a_n\equiv a_m\pmod{5^{\min(e_n,e_m)}}.
$$

Put

$$
 F_{\mathcal P}(y)=
    \sum_{\{n,m\}\in\mathcal P}
       \frac{5^{-\max(e_n,e_m)}}{\rho}
                         \mathbf1_{C_n\cap C_m}(y).
$$

Then $\mathcal O(y)\ge F_{\mathcal P}(y)$ throughout $R_5$.
At a five-coordinate with multiplicity $m\ge1$, at most
$\lfloor m/2\rfloor\le m-1$ matched pairs occur; outside the
reached hole the available charge is the larger value $m$.
A compatible pair has exactly
$5^{G-\max(e_n,e_m)}$ common five-coordinate points. Summing
these pointwise inequalities proves

$$
 \begin{aligned}
 k\int_{R_5}\min\{s,F_{\mathcal P}(y)\}\,d\nu(y)&\le S,\\
 \frac{k\,5^{-\max(e_n,e_m)}}{\rho}
       \nu(R_5\cap C_n\cap C_m)&\le S
               \quad\text{for one compatible pair}.
 \end{aligned}
 \tag{CD205}
$$

The second line uses
$5^{-\max(e_n,e_m)}/\rho\le1/(25\rho)\le s$, so a single
pair needs no clipping. A matching with several pairs still
requires the clipping shown in the first line. Their cofactor
intersections and blockers are evaluated under the same $\nu$;
product structure alone gives no lower bound for those intersections.

The remaining sufficient source assertion is now precise: some
admissible live-root budget must satisfy
$\int_{R_5}\min\{s,\mathcal O\}\,d\nu>S/k$.
A stronger sufficient assertion is the same strict inequality
with one actual-label $F_{\mathcal P}$ in place of $\mathcal O$.
Neither the positive reserve nor the existence of at least two
suppliers forces this excess or compatible-pair mass. These
certificates, the two-sided charge bounds and the shallow debit
are alternative lower bounds on the same $\mathfrak D_*$ and
cannot be added again without disjoint accounting.

CD198–CD205 are ordinary finite mathematical deductions. A scoped
transient Lean check verifies their finite rational-law accounting
components: the common original-event majorant, nonnegative slot losses,
the exact total-budget decomposition, the restricted deep-loss identity,
and the distinguished unit-prefix deficit and coordinate boost. Its
joint application uses the same source law, original event family and
prefix data, including equality of the distinguished prefix with the
local first-five fibre. The complete hole quantifies over every supplied
retained original index. All checked axiom closures contain only
`propext`, `Classical.choice` and `Quot.sound`.

The actual integer-family construction of those data and incidence
premises has not been kernel-checked. In particular, the distinguished
label's modulus being 45, its quantitative deficit, the original-family
classification of deleted indices, and the complete-source exclusions
remain arithmetic bridge obligations. The aggregate shallow-loss
combination and CD176's scalar envelope were not checked by this
application. The final original-family $S$ budget and unrestricted
Erdős #7 are not thereby Lean verified. These checks directly reuse
finite-law and cardinality results and add no frozen declarations.

## Fixed exceptional originals and different-color tuple moments

### Original source and the fixed exceptional set

Keep one EB1 original odd distinct nonunit whole cover with actual3,
actual9, ternary height at most two and shared-prime set `{5}`. Keep
one selected root, its safe full words `J`, `k=|J|` in `{2,3}`, and
one fixed guarded ordinary product law `lambda`. All residues,
numerical labels, five depths and ordinary coordinate laws refer to
that same original family. Write

$$
 Q=5^G N,\qquad N=9M,\qquad (M,15)=1,\qquad G\ge2,
 \qquad \nu=U_J\otimes\lambda.
$$

Use Report850 CD186–CD205's complete five-free cofactor source `Y`,
first-five phase `omega`, and complete deletion of all ordinary-bearing
positive-five originals. Every unit label `5^e,3*5^e,9*5^e` is retained,
including actual75 and actual225. This is not the narrower Q2P deletion.
Let `I` be the words left after the actual45 exclusion, and let `Y_j`
be the actual ordinary source slice. For `j` outside `I`, `Y_j` is empty.
The literal private25 set remains null under the guarded full law;
`nu(Y)` is the non-five source mass and can be positive.

For each `j`, [Report385 GLC1](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#172-literal-prime-root-collisions-have-one-fixed-exceptional-pair-across-all-sources) is applied to all actual top originals
with full ternary word `j` and first-five phase `omega`, over all
positive five depths. It supplies one set `X_j` of at most two
original labels meeting every literal ordinary prime-root collision
edge. The choice is made before any ordinary point is fixed. Thus
outside that same `X_j`,

$$
 n\ne f,\quad \gcd(m_n,m_f)>1
 \quad\Longrightarrow\quad
 C_n^{\rm ord}\cap C_f^{\rm ord}=\varnothing.                 \tag{CD206}
$$

The labels of `X_j` remain in the cover. Only its intersection with
the actual deep ordinary-bearing top labels will contribute to the
exceptional loads below. A point-dependent choice of `X_j` would not
justify the moment identity.

The consumer permits any fixed set meeting all collision edges.
An empty graph permits the empty set; a star permits its center;
a triangle permits two vertices. The GLC1 source proof needs only the
two endpoints of any edge. One may minimize the consumer over all
valid fixed choices without changing the actual source or its law.

**Verification boundary.** The fixed-set source step for this
ternary-height-two, q=5 regime is verified by the repository's
[`exists_fixed_collision_exceptions`](https://github.com/the-omega-institute/trureturing/blob/d14bae95b1c0bca6860b064d070ffd4229a81bbe/D5/S3/Arith/Covering/FixedCollisionExceptions.lean#L341).
Its carrier covers every natural number, with distinct odd nonunit
moduli, no original modulus divisible by27, and minimum modulus sum
among all same-count covers, with unrestricted competitor heights.
It preserves every deleted congruence class and selects X before any
cofactor point or probability law. The general all-height GLC1 statement
in Report385 and the different-color moment/source consumer below remain
ordinary mathematical derivations. No separate integer-carrier
specialization or entire consumer chain is claimed as Lean-verified.

### Actual loads retain low rows and exceptional labels

For `j` in `I`, let `C_j` be the available second-five digits after
actual25 and the active depth-two unit labels75 and225. It has two,
three or four members. For `c` in `C_j`, retain the exact residual
unit-hole density `delta_{j,c}` on the complete second-five fibre:

$$
 \delta_{j,c}\ge h_G:=\frac14+\frac34\,5^{2-G}>0.
                                                               \tag{CD207}
$$

This is Report850 CD194; it retains every higher unit tower. In
particular `delta_{j,c}=1` when `G=2`.

All following index sets consist of actual original labels with
`e_n>=2`, `m_n>1`, first-five phase `omega` and second-five color `c`.
Use the actual weight

$$
 w_n=5^{2-e_n}.
$$

Let `L_c` index the active low-row originals, with ternary height at
most one. Let `T_{j,c}` index the top originals at full word `j`.
Set `E_{j,c}=T_{j,c}\cap X_j` and `T^0_{j,c}=T_{j,c}\setminus X_j`.
Define functions on the same ordinary carrier:

$$
 \begin{aligned}
 l_c(y)&=\sum_{n\in L_c}w_n\mathbf1_{C_n^{\rm ord}}(y),\\
 x_{j,c}(y)&=\sum_{n\in E_{j,c}}w_n\mathbf1_{C_n^{\rm ord}}(y),\\
 h_{j,c}(y)&=\sum_{n\in T^0_{j,c}}w_n\mathbf1_{C_n^{\rm ord}}(y).
 \end{aligned}                                                 \tag{CD208}
$$

Each low function `l_c` is shared by every safe word of the root.
Each top original has one actual word and one actual color. Repeated
numerical cofactors at different five depths remain separate original
indices. None of these functions is a replacement event or a freely
assignable scalar capacity.

The complete same-color residual hole must be covered by these
originals at every point of the source, so the original fibre union
bound gives

$$
 y\in Y_j\quad\Longrightarrow\quad
 l_c(y)+x_{j,c}(y)+h_{j,c}(y)\ge\delta_{j,c}.
                                                               \tag{CD209}
$$

Write the full-law integrals as

$$
 L_c^*=\int l_c\,d\lambda,\qquad
 X_{j,c}^*=\int x_{j,c}\,d\lambda,\qquad
 H^0_{j,c}=\int h_{j,c}\,d\lambda.
$$

The existing inventories are retained jointly:

$$
 \sum_cL_c^*\le2A_GW,\qquad
 \sum_{j,c}(X_{j,c}^*+H^0_{j,c})\le A_GW,
 \qquad A_G=\sum_{e=2}^{G}5^{2-e}=\frac54(1-5^{1-G}).             \tag{CD210}
$$

They cannot be allocated independently at each word or optimized
independently of the source. If four colors are available, at least
two contain no exceptional labels because `|X_j|<=2`. Choosing those
two colors removes their exceptional term, but does not remove their
shared low-row load.

### The exact different-color tuple moment

For any nonempty subset `K` of `C_j`, let

$$
 Z_{j,K}=\sum_{\substack{n_c\in T^0_{j,c}\ (c\in K)\\
                         m_{n_c}\ \text{pairwise coprime}}}
              \prod_{c\in K}w_{n_c}\lambda(C_{n_c}^{\rm ord}).    \tag{CD211}
$$

The sum is over actual tuples of original indices, one index for each
different color. Empty index families yield zero. Repeated numerical
cofactors have not been merged, and the pairwise-coprime condition is
on the cofactors of the chosen original indices.

Expanding the product of the finite sums in CD208 gives a term for every
such actual tuple. A tuple with a noncoprime pair has empty ordinary
intersection by CD206. In every remaining tuple the ordinary prime
supports are disjoint, so independence under the complete product
law gives its intersection probability as the product of its actual
marginal probabilities. Therefore

$$
 \boxed{\int\prod_{c\in K}h_{j,c}(y)\,d\lambda(y)=Z_{j,K}.}      \tag{CD212}
$$

This uses the coprime-disjoint intersection expansion of [Report387 CC12](../350-399/387-cyclic-crt-prime-capacity-and-forced-crowded-stars.md#3-explicit-survivors-give-strict-positivity), with actual-index depth weights and guarded product marginals.
It does not import that report's uniform-Haar positivity or Shearer
transfer: their divisor-palette and Haar hypotheses have not been
provided here. Independence is used on the full product law, never
asserted after conditioning on `Y_j`.

From CD209, all factors are nonnegative and

$$
 \boxed{\int_{Y_j}\prod_{c\in K}
       [\delta_{j,c}-l_c(y)-x_{j,c}(y)]_+\,d\lambda(y)
       \le Z_{j,K}.}                                          \tag{CD213}
$$

This is the common-source relation retaining the actual tuple data,
the same low-row functions and the fixed exceptional suppliers.

For positive `delta_c` and nonnegative `a_c`, the elementary product
inequality

$$
 \prod_c(\delta_c-a_c)_+
 \ge\Bigl(\prod_c\delta_c\Bigr)
          \left(1-\sum_c\frac{a_c}{\delta_c}\right)             \tag{CD214}
$$

follows from `prod(1-b_c)>=1-sum b_c` for `0<=b_c<=1`, taking
`b_c=min(a_c/delta_c,1)`. Integrating CD214 in CD213 gives

$$
 \lambda(Y_j)\le
 \sum_{c\in K}\frac{\int_{Y_j}(l_c+x_{j,c})\,d\lambda}
                        {\delta_{j,c}}
 +\frac{Z_{j,K}}{\prod_{c\in K}\delta_{j,c}}.                   \tag{CD215}
$$

Thus the following entirely actual full-law quantities are upper
bounds:

$$
 \begin{aligned}
 \Theta_{j,K}(X_j)
   &=\sum_{c\in K}\frac{L_c^*+X_{j,c}^*}{\delta_{j,c}}
       +\frac{Z_{j,K}}{\prod_{c\in K}\delta_{j,c}},\\
 \Theta_j
   &=\min\left(1,\min_{\substack{X_j\ \text{valid fixed}\\
                          \varnothing\ne K\subseteq\mathcal C_j}}
                       \Theta_{j,K}(X_j)\right),\\
 \Theta_{\rm tuple}&=\frac1k\sum_{j\in I}\Theta_j,
 \qquad \boxed{\nu(Y)\le\Theta_{\rm tuple}.}
 \end{aligned}                                                 \tag{CD216}
$$

Here a valid fixed `X_j` is a subset of the original top labels, has
cardinality at most two, and meets every collision edge for that word.
One may instead keep a single supplied valid `X_j` in the minimum.
For a singleton `K={c}`, `Z_{j,K}=H^0_{j,c}` and
`X_{j,c}^*+H^0_{j,c}` is the complete top load in that color.
Consequently the singleton term is exactly the CD195 bound;
the minimum retains it and adds the different-color restrictions.
CD215 is stronger when the source-restricted low and exceptional
integrals are known.

### Optional finite-palette enlargement

Let `A` be the active ordinary palette and `g_p=1/(p-3)`, with
`W=prod_p(1+g_p)-1`. For each active ordinary prime `p`, the selected law of CD164 and
CD187 is uniform on the complement `Z_p` of the actual pure-`p`
prefixes and the actual `3*p^a` prefixes at the selected root.
Let `H_p=v_p(Q)` and `rho_p=|Z_p|/p^{H_p}`. Numerical distinctness
permits at most one label in each of these two towers at each depth.
The same one-coordinate union bound gives

$$
 \rho_p\ge1-2\sum_{a=1}^{H_p}p^{-a}
      \ge\frac{p-3}{p-1}>0.
$$

For every actual literal depth-`a` prefix its conditional probability
is at most `p^{-a}/rho_p`. Set

$$
 \eta_{p,a}=\frac{p^{-a}}{\rho_p}\quad(1\le a\le H_p),\qquad
 \widetilde g_p=\sum_{a=1}^{H_p}\eta_{p,a}
       \le\frac1{p-3}=g_p.
$$

Product independence on the actual guard complements now gives

$$
 \lambda(C_n^{\rm ord})\le\prod_{p^a\parallel m_n}\eta_{p,a}
                                                               \tag{CD217}
$$

for the surviving actual originals supported on the active palette.
Every original bearing an opposite-root prime is excluded by its
fixed singleton coordinate; this statement concerns actual original
events, not arbitrary prefixes under a point-mass law. Thus zero
terms can first be removed. The displayed caps are derived from the
existing selected-law guards, not assumed for an arbitrary law.

For a top original, distinctness of the numerical labels makes
`n -> (e_n,m_n)` injective. Apply CD217 to the literal probabilities in
CD211, then enlarge the sum to all numerical depth/cofactor slots.
The separate depth sum is `A_G` for each tuple entry. In a tuple of
pairwise coprime nonunit cofactors each ordinary prime belongs to at
most one color, and every color receives at least one prime. Hence,
with `h=|K|`,

$$
 \boxed{Z_{j,K}\le A_G^hF_h(\widetilde g)\le A_G^hF_h(g),}
 \qquad
 F_h(g)=\sum_{a=0}^{h}(-1)^{h-a}\binom ha
                    \prod_{p\in A}(1+a g_p).                  \tag{CD218}
$$

The positive interpretation of `F_h` assigns each prime either to
unused or to one of the `h` colors, requires each color to be used,
and multiplies the `g_p` of all assigned primes. This proves
nonnegativity and coordinatewise monotonicity. Inclusion-exclusion
on missing colors gives the displayed alternating expression.
In particular,

$$
 F_1=W,\qquad
 F_2=\prod_p(1+2g_p)-2\prod_p(1+g_p)+1,\qquad
 0\le F_h\le W^h.                                              \tag{CD219}
$$

If the palette has fewer than `h` primes, then `F_h=0`. Repeated
cofactors at different five depths are accounted for by their
separate original depth slots; no numerical cofactor identification
was used in CD211 or CD212.

For the fixed palette `A={7,17,23,37}` and `G=4`, exact substitution
gives `W=487/1088` and `A_G=31/25`:

| h | F_h(g) | A_G^h F_h(g) |
| --- | --- | --- |
| 2 | 1931/19040 | 1855691/11900000 |
| 3 | 117/9520 | 3485547/148750000 |
| 4 | 3/4760 | 2770563/1859375000 |

Each displayed tuple allowance is strictly smaller than `(A_G W)^h`.
These values are exact evaluations of one fixed formula and palette,
not a palette scan or a noncoverage certificate. The low-row and
exceptional contributions in CD215–CD216 remain payable.

### Consumer of the existing excess budget

Let `a=nu(Y)`, `zeta_0=nu(R_5)`, and retain the exact same-source
normalized deep demand `t=integral_Y(q/d) dnu`. The CD200 common-budget
bound is

$$
 s(\zeta_0-a)+c(t-a)\le\mathfrak D_*\le S/k,
 \qquad c=\frac{d_G}{5\rho},\qquad
 S=(k-r)\bar L+(2k+1)bW+D-M_k(r).                               \tag{CD220}
$$

All its variables refer to the same actual source, unit residuals,
ordinary product law and original phases as CD208–CD216. Since
`a<=zeta_0`, `a<=t` and `a<=Theta_tuple`,

$$
 \boxed{s\zeta_0+ct-(s+c)\min(\zeta_0,t,\Theta_{\rm tuple})
          \le\mathfrak D_*\le S/k.}                           \tag{CD221}
$$

For `S>=0`, a sufficient closing condition is that the left side of
CD221 exceed `S/k`. A weaker sufficient condition is

$$
 k s[\zeta_0-\Theta_{\rm tuple}]_+>S.                          \tag{CD222}
$$

No uniform instance of either strict inequality has been established.
Low-row supply and the fixed exceptional originals can absorb color
demand, and the separate source, tuple and inventory extrema cannot
be assumed jointly attainable.

Different second-five colors have disjoint five-prefix fibres.
CD212–CD216 therefore bound the non-five source mass; they do not assert
same-five-prefix overlap and cannot be substituted directly into
CD205's overlap debit. Their route to a debit is CD190 or CD220–CD221.
The actual45 term is already charged once inside `D_*`; no additional
`r -> r-s` payment is introduced.

No Lean verification of the CD207–CD222 moment/source consumers or unrestricted Erdős #7 conclusion
is asserted.

## A complete local hole can be tiled with zero excess

The positive complete-hole reserve and two actual deep suppliers do not
force positive raw excess without further whole-cover restrictions.
Consider this explicit family, with common period $Q=32175$:

| Modulus | Residue | A private point modulo $Q$ |
| ---: | ---: | ---: |
| 3 | 0 | 4728 |
| 5 | 1 | 30611 |
| 9 | 1 | 15310 |
| 11 | 0 | 18040 |
| 13 | 0 | 25870 |
| 15 | 13 | 29038 |
| 25 | 0 | 19600 |
| 33 | 1 | 15115 |
| 39 | 1 | 13495 |
| 45 | 22 | 5872 |
| 55 | 25 | 9265 |
| 65 | 55 | 20920 |
| 75 | 55 | 17455 |
| 99 | 13 | 12190 |
| 117 | 67 | 1120 |
| 165 | 70 | 6340 |
| 195 | 160 | 8545 |
| 225 | 85 | 4585 |
| 275 | 215 | 490 |
| 325 | 45 | 15970 |
| 495 | 445 | 3415 |
| 585 | 265 | 28345 |
| 825 | 40 | 29740 |
| 975 | 670 | 3595 |
| 2475 | 2065 | 26815 |
| 2925 | 2920 | 23395 |

These are exactly the nonunit divisors of 2475 or 2925. All moduli are
odd and distinct, and all ternary and five depths are at most two.
Every listed private point has its indicated class as its unique owner.
Every proper comparable pair of originals has incompatible residues.
The qualifying full-ternary DR8 parents are 225, 495, 585, 2475 and
2925; each of their proper-descendant phase buckets has at most two
original labels.

The entire first-five-zero fibre above the five-free source
$y=580\pmod{1287}$ consists of the following five points. Its ordinary
coordinates are $8\pmod{11}$ and $8\pmod{13}$, and its full ternary
word is $4\pmod9$.

| Five coordinate modulo 25 | Point modulo $Q$ | Unique original owner modulus |
| ---: | ---: | ---: |
| 0 | 13450 | 25 |
| 5 | 580 | 75 |
| 10 | 19885 | 225 |
| 15 | 7015 | 2475 |
| 20 | 26320 | 2925 |

In particular 13450 is private to the actual25 original, so 580 is
in its complete five-free projection. Delete all and only originals
with positive five depth and nonunit ordinary cofactor. The retained
family still includes every present unit, including 25, 75 and 225.
Its complete hole in this fibre is exactly the two points with five
coordinates 15 and 20. Thus the hole has relative size $2/5>1/4$.

The actual originals of moduli 2475 and 2925 meet those two points
respectively, with disjoint singleton traces. They exactly tile the
hole, so their raw deep excess is zero. Under the same pure-five and
root-specific unit guards, the five complement has 13 points, three
at first-five phase zero. Hence $\rho=13/25$, $\gamma=3/13$ and
$s=2/13>0$: positive guard loss also does not force a local excess.

A transient Lean check verifies this literal family, all displayed
private witnesses, divisor and phase conditions, the complete CRT
fibre, exact retained hole, its disjoint original suppliers and the
zero excess. It also verifies that 23890 is uncovered by every
original. Its axiom closures are contained in the standard set
`propext`, `Classical.choice`, `Quot.sound`; no new frozen declaration
is introduced.

This is a noncover, so it cannot realize EB1 or contradict the
whole-cover budget. It rules out the implication from the displayed
local restrictions alone to positive excess. The required whole-source
service and global replacement restrictions remain additional inputs.

## Two-word escape charges the same original excess

Keep one EB1 original odd distinct nonunit whole cover, actual3 and9,
ternary height at most two, and shared-prime set `{5}`. Keep one live
ternary root with safe full words `J`, `k=|J|` in `{2,3}`, and the same
guarded ordinary product law `lambda` as CD186--CD205. Write

$$
Q=9\cdot5^G M,\qquad (M,15)=1,\quad G\ge2,
\qquad \nu=U_J\otimes\lambda.
$$

All labels, residues and sections below belong to this one family.
Write an original modulus as `3^h 5^e m`, with `(m,15)=1`.
The first-five phase `omega` is the phase of the actual25 original.
The deletion removes exactly all originals with `e>=1` and `m>1`.
Every unit original `5^e`, `3*5^e`, `9*5^e` remains, including75,
225 and every higher unit. Let `E_(u,w)` be the complete hole of
all retained originals, restricted to the first-five fibre `B_omega`.

Let `R_u` be the section at full word `u` of the complete five-free
survivor `R_5`. Let `Y_v` be the section at `v` of the complete
private25 cofactor source `Y`: it excludes every five-free original
and every first-five-depth cofactor cylinder at phase `omega`,
including unit exclusions. These are actual sets in the same
ordinary carrier. A selected private witness or a narrower deletion
source cannot replace either complete set.

For every original deep ordinary supplier `n` with first phase
`omega`, retain its literal ambient five-prefix `P_n` in
`Z/(5^G)` and its complete cofactor incidence at `(u,w)`.
Let `V_T(u,w)` be the union of these incident prefixes. The existing
raw excess and clipped word debit are

$$
\begin{aligned}
O(u,w)&=\frac{\sum_{n\in\mathcal T}
          \mathbf1_{C_n}(u,w)|P_n|
          -|E_{(u,w)}\cap V_{\mathcal T}(u,w)|}{|Z_5|},\\
\mathcal D_u&=\int_{R_u}\min(s,O(u,w))\,d\lambda(w),
\qquad \sum_{u\in J}\mathcal D_u\le S.
\end{aligned}                                                    \tag{CD223}
$$

Here `rho=|Z_5|/5^G` and `s>=1/(25*rho)>0` are unchanged from
CD203--CD205. The last inequality is exactly the existing bound
`k integral_(R_5) min(s,O) dnu <= S`. Raw prefixes may extend
outside `Z_5`; their unused allowances remain part of `O`.

### Guarded descendants retain a uniform conditional bound

At an active ordinary prime `p`, the coordinate law is uniform on
the actual guard complement `Z_p`. The guards consist of the pure
`p^a` prefixes and the applicable `3*p^a` prefixes at this root,
with at most two forbidden prefixes at each positive depth.
Let `C` be a literal depth-`a` prefix with `C intersect Z_p` nonempty;
depth zero means the whole coordinate. No guard of depth at most
`a` can contain `C`, since prefixes in one prime coordinate are
nested or disjoint. Only deeper guards can remove points of `C`.
For any literal proper descendant prefix `D` of `C` and ambient prime
height `H_p`, their union bound gives

$$
\frac{|C\cap Z_p|}{|C|}
\ge1-2\sum_{r=1}^{H_p-a}p^{-r}
\ge\frac{p-3}{p-1}.
\qquad
\frac{|D\cap Z_p|}{|C\cap Z_p|}
\le\frac{p-1}{p(p-3)}\quad(D\subsetneq C).
                                                               \tag{CD224}
$$

The second bound uses `|D|<=|C|/p`. It conditions on the actual
live prefix `C`; an unconditional coordinate cap alone would not
justify it. All active ordinary primes are at least7. Define

$$
\eta_{\mathcal A}=\max\left\{\frac15,
       \max_{p\in\mathcal A}\frac{p-1}{p(p-3)}\right\}
\le\frac3{14}.
\qquad
7\notin\mathcal A\ \Longrightarrow\ \eta_{\mathcal A}=\frac15.
                                                               \tag{CD225}
$$

For an empty active palette the maximum is `1/5`.
At `p=7` the ordinary bound is `3/14`; for `p>=11` it is below
`1/5`. Opposite-root coordinates are fixed at their established
singletons. An original section annihilated by those coordinates
has zero mass and may be omitted. This exclusion concerns the
actual original classes, not arbitrary prefixes under a point mass.

For a high original `i`, put `d_i=5^(e_i)*m_i`, and write
`C_i^ord` for its literal ordinary section. Assume
`lambda(C_i^ord)>0` and set `alpha_i=|P_i|/|Z_5|`.
For another live high original `b`, ambient section containment is

$$
P_i\times C_i^{\rm ord}\subseteq P_b\times C_b^{\rm ord}
\quad\Longleftrightarrow\quad
d_b\mid d_i\ \text{ and }\ a_i\equiv a_b\pmod{d_b}.
                                                               \tag{CD226}
$$

The comparison omits only the ternary coordinate; different full
words remain attached to the two original labels. If containment
fails, incompatible prefixes give an empty intersection. Otherwise
some coordinate of `b` imposes an additional digit on `i`.
A five-digit costs at most `1/5`; an ordinary digit costs at most
CD224, including when `i` has depth zero in that coordinate. Thus

$$
\beta_{ib}:=\frac{|P_i\cap P_b|}{|Z_5|}
      \lambda(C_i^{\rm ord}\cap C_b^{\rm ord})
\le\eta_{\mathcal A}\alpha_i\lambda(C_i^{\rm ord}).             \tag{CD227}
$$

The factorization is under the full product law `lambda`, or its
conditioning on the rectangular literal section `C_i^ord`.
No independence after conditioning on `R_u`, `Y_v` or their
intersection is asserted. The five factor is a raw cardinal ratio,
not a replacement probability law on the five-coordinate.

### Escape from another word forces loss at the original word

Choose an actual high deep ordinary original
`n_i=9*5^(e_i)*m_i`, with `e_i>=2`, `m_i>1`, full word `u`,
first-five phase `omega`, and positive ordinary-section mass.
Put `tau_i=a_i mod25`. Choose a different safe word `v` such that
the phase `(v mod9,tau_i mod25)` is not the actual225 phase.
Let `B_(v,tau_i)` contain every proper original multiple of225
in that phase. It includes all high unit originals `9*5^e` there.
[Report385, DR8](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md)
gives

$$
|\mathcal B_{v,\tau_i}|\le2.                                  \tag{CD228}
$$

Assume no member with nonzero actual ordinary section contains
`i`'s section in CD226. Define the unmasked raw escape function

$$
e_{i\to v}(w)=\frac{\mathbf1_{C_i^{\rm ord}}(w)}{|Z_5|}
\left|P_i\setminus
  \bigcup_{\substack{b\in\mathcal B_{v,\tau_i}\\w\in C_b^{\rm ord}}}P_b
\right|.                                                       \tag{CD229}
$$

Take `w in R_u intersect Y_v` and a five-coordinate `z` counted
by CD229. Apply whole original coverage to the actual CRT point
`(v,w,z)`, including when `z` lies outside `Z_5`. The complete
definition of `Y_v` excludes every five-free original and every
depth-one original at first phase `omega`. A high original of
five depth at least two would lie in the bucket CD228, except for
actual225 itself; that label was excluded by the phase condition.
All bucket owners were removed from CD229. Therefore some covering
original has ternary height at most one and five depth at least two.

Such a low original also covers `(u,w,z)`, since `u` and `v` have
the same ternary root. Outside the retained hole, `i`'s full raw
slot is charged by `O`. Inside the hole the low owner cannot be a
retained unit, so it is an ordinary-bearing member of `T`, distinct
from high original `i`. The deep multiplicity is then at least two
and the reached-hole term subtracts at most one. Consequently

$$
\mathbf1_{Y_v}(w)e_{i\to v}(w)\le O(u,w)\quad(w\in R_u),
\qquad
0\le e_{i\to v}(w)\le\alpha_i
=\frac1{\rho5^{e_i}}\le\frac1{25\rho}\le s.                    \tag{CD230}
$$

This is a statement about the complete intersection `R_u intersect
Y_v`. Neither survivor can be discarded from the debit implication.
The last scale bound allows this single contribution through the
existing clipping. Integrating the raw union bound in CD229 gives

$$
\begin{aligned}
\mathcal D_u
&\ge\alpha_i\lambda(C_i^{\rm ord}\cap R_u\cap Y_v)
       -\sum_{b\in\mathcal B_{v,\tau_i}}\beta_{ib},\\
\mathcal D_u
&\ge\alpha_i\left[
   \lambda(C_i^{\rm ord}\cap R_u\cap Y_v)
   -|\mathcal B_{v,\tau_i}|\eta_{\mathcal A}
             \lambda(C_i^{\rm ord})\right]_+.
\end{aligned}                                                   \tag{CD231}
$$

In the first line the nonnegative opponent intersections over the
source were bounded above by their full-law values `beta_ib`.
No conditional-product estimate on the source is used.
Using CD225 and CD228 replaces the loss coefficient by `3/7`, or by
`2/5` when7 is inactive. If all of `C_i^ord` survives in the two
required sections up to a null set, then

$$
\mathcal D_u\ge\frac47\alpha_i\lambda(C_i^{\rm ord}),
\quad\text{or }\frac35\alpha_i\lambda(C_i^{\rm ord})
             \text{ when }7\notin\mathcal A.                   \tag{CD232}
$$

For an admissible comparison phase, a bound `D_u<=epsilon`
therefore forces either an actual containing opponent or

$$
\lambda(C_i^{\rm ord}\setminus(R_u\cap Y_v))
\ge\frac47\lambda(C_i^{\rm ord})-\rho5^{e_i}\varepsilon.        \tag{CD233}
$$

### A packet charges each unit of the same debit once

For each target word `u`, select a finite set `I_u` of distinct
actual high originals at that word. Fix for each label its own
comparison word `v_i` satisfying the preceding phase and
noncontainment conditions. Require the raw-capacity condition

$$
\sum_{i\in I_u}\alpha_i\le s.                                 \tag{CD234}
$$

The pointwise packet function must retain each label's source mask:

$$
F_u(w)=\sum_{i\in I_u}\mathbf1_{Y_{v_i}}(w)e_{i\to v_i}(w).
                                                               \tag{CD235}
$$

Fix `w in R_u` and one raw five-coordinate. Let `r` count selected
high labels whose masked contributions reach that coordinate.
Outside the retained hole all `r` raw slots are charged. Inside
the hole, if `r>0`, coverage at any one of the corresponding
comparison words supplies an additional low ordinary owner at `u`.
It is distinct from all `r` high labels. The deep multiplicity is
at least `r+1`, and subtracting the reached-hole indicator leaves
at least `r`. The case `r=0` uses nonnegativity. Summing coordinates
and using CD234 proves

$$
0\le F_u(w)\le O(u,w),\qquad F_u(w)\le s,
\qquad F_u(w)\le\min(s,O(u,w))\quad(w\in R_u).                  \tag{CD236}
$$

The unmasked sum of CD229 has no such asserted bound. Its summands
may lack the complete `Y_(v_i)` condition needed to force low
service. Integrating CD236, then applying the separate nonnegative
escape integrals as in CD231, yields

$$
\begin{aligned}
k\int_{R_5}\min(s,O)\,d\nu
\ge\sum_{u\in J}\sum_{i\in I_u}\alpha_i
\Big[\lambda(C_i^{\rm ord}\cap R_u\cap Y_{v_i})
-|\mathcal B_{v_i,\tau_i}|\eta_{\mathcal A}
       \lambda(C_i^{\rm ord})\Big]_+.
\end{aligned}                                                   \tag{CD237}
$$

The exact-intersection summand is
`[alpha_i*lambda(C_i^ord intersect R_u intersect Y_(v_i))
  - sum_b beta_ib]_+`.
The addition in CD237 follows from the multiplicity argument CD236;
it is not addition of separate lower bounds on the same debit.
CD223 and CD237 give a sufficient contradiction criterion:

$$
\sum_{u\in J}\sum_{i\in I_u}\alpha_i
\Big[\lambda(C_i^{\rm ord}\cap R_u\cap Y_{v_i})
-|\mathcal B_{v_i,\tau_i}|\eta_{\mathcal A}
       \lambda(C_i^{\rm ord})\Big]_+>S.                        \tag{CD238}
$$

### Arithmetic meaning and the unproved extraction step

A containing high opponent has `d_b | d_i` with compatible
five/ordinary phases. Both full moduli have ternary exponent two,
so `n_b | n_i`; numerical distinctness gives `n_b<n_i`.
These actual ancestor relations are acyclic and may terminate at
a retained high unit. Their full original APs still have different
ternary words. Section containment does not authorize moving them.

No result here forces an admissible packet with CD238, sufficient
common-section mass, or the required absence of containing
ancestors. The two root laws remain separate, and the root without
active7 need not carry enough source mass. The bound may vanish
when the comparison `Y_v` is empty, for example when `k=2` and
actual45 at phase `omega` leaves only one available source word.
An effective different comparison word is not guaranteed.
The two-supplier local noncover does not supply the whole-coverage
implication used in CD230 or CD236.

Five-fibre tree contraction also does not supply a full-label
integer replacement: different leaves may have different ordinary
cofactors and complete old regions. The related extraction and
literature boundaries in [Report853, section8](853-paid-packet-absorption-and-residual-moment.md#8-literature-mechanisms-and-the-remaining-extraction-problem)
remain applicable. No literature theorem is used to infer CD238.
CD237 is another lower bound on the already paid quantity in CD223;
it is not added again to the actual45 charge or the CD200 debit.
These are conditional ordinary mathematical deductions; no Lean verification or unrestricted Erdős #7 conclusion is asserted.

## All cofactors pay the untruncated deep excess

Keep one globally count-minimal, then same-count modulus-sum-minimal odd distinct nonunit whole cover. Both comparison classes consist of all odd distinct nonunit whole covers. Assume actual3 and actual9, ternary height at most two, shared-prime set `{5}`, and five-height `G>=2`. Write

\[
Q=9\cdot5^G M,\qquad (M,15)=1,\qquad
n=3^{h_n}5^{e_n}m_n,\quad (m_n,15)=1.
\]

Fix one live ternary root whose complete private25 cofactor source has positive selected mass. Keep its actual safe words `J`, the guarded ordinary product law `lambda`, and `nu=U_J tensor lambda`. Let `Z=Z_5`, `rho=|Z|/5^G`, and let `B=B_omega` be the first-five phase of the actual25 original. All cylinders and phases below belong to the same original family. Actual events annihilated by opposite-root singleton coordinates contribute zero; no arbitrary prefix under a point mass is declared impossible.

Delete exactly

\[
\mathcal M=\{n:e_n\ge1,\ m_n>1\}.
\]

The complete hole `E_M` is the complement of every retained original, including all five-free originals and every unit original `5^e,3*5^e,9*5^e`. For every selected cofactor `y`, not only `y in R_5`, put

\[
E_y=\{z\in B:(y,z)\in E_{\mathcal M}\}.
\]

The fixed shallow and deep original sets are

\[
\begin{aligned}
\mathcal H&=\{n:e_n=1,\ m_n>1,\ a_n\equiv\omega\pmod5\},\\
\mathcal T&=\{n:e_n\ge2,\ m_n>1,\ a_n\equiv\omega\pmod5\}.
\end{aligned}
\]

A scoped transient Lean check verifies the finite rational-law core of this extension: the reached-hole charge and its domination by the complete majorant, exact full-prefix cancellation, disjoint shallow/deep allocation, the retained-unit blocked-word identity, and the two-word budget. It also verifies the scalar lower inequality used below. All checked declarations use only the standard axioms. The full original-integer routing, literal modulus45 identification, arithmetic prefix-size normalization, old scalar envelope and scalar infimum attainment remain ordinary mathematical steps, not conclusions of that check. No unrestricted Erdős #7 conclusion is asserted.

The argument reuses CD186–238, the literal collision theorem of Report385 §172, and the complete-liability boundaries in Report853 §8. The numerical `q=113` code geometry of Report853 is not used at `q=5`.

### Full cofactor support pays the unclipped excess

Reuse Report850 CD198–199, with the same individually counted original set `I_ind`, complete low five-free union `L0`, high unit-five union `V5`, high ordinary-axis union `Vo`, raw allowances `u_n`, and majorant

\[
F=1_{L_0}+\sum_{n\in I_{\rm ind}}1_{A_n}
  +1_{L_0^c}\{1_{V_5}+(1-1_{V_5})1_{V_o}\}.
\tag{CD239}
\]

Let `Braw` denote CD199's `mathcal B`, and `beta=chi*s*c_(j0)/k`. Then

\[
\begin{aligned}
F&\ge1,\\
B_{\rm raw}-1
 &=\sum_{n\in I_{\rm ind}}(u_n-\mu(A_n))+\int(F-1)\,d\mu,\\
B_{\rm raw}-1+\beta&\le S/k.
\end{aligned}
\tag{CD240}
\]

All losses and the overcount are nonnegative. Both H and T are subsets of `I_ind`, and they are disjoint. The upper bound in CD240 retains the original axis-envelope hypotheses of CD188–199, including the same valid caps `b,r`, the bound `ell<=Lbar<=P`, and the same definition of S. The finite-event identity alone does not supply that numerical envelope.

For actual `n in T`, keep its entire ambient prefix `P_n=[a_n]_(5^e_n)`, including points outside `Z`. Define

\[
\begin{aligned}
V_T(y)&=\bigcup_{n\in\mathcal T,\ y\in C_n}P_n,\\
O_{\rm all}(y)&=
 \frac{\sum_{n\in\mathcal T}1_{C_n}(y)|P_n|
             -|E_y\cap V_T(y)|}{|Z|}.
\end{aligned}
\tag{CD241}
\]

This extends CD203's exact function to every selected cofactor. It is nonnegative by the elementary union bound. It does not redefine the deleted family, replace the complete hole, or change the source law.

#### Retained-owner classification

On the complete sampled support, every retained original with a nonempty actual event is represented by a contribution outside T in CD239:

- A low five-free event is in `L0`, except actual guard events, which have zero selected event.
- A high five-free event is either an ordinary axis in `Vo` or a nonaxial event in `I_ind \ T`.
- A positive-five unit event in a low row is a pure-five or applicable `3*5^e` guard and is absent on `Z`.
- A positive-five high unit event belongs to `V5`.
- Pure3 and pure9 are absent at the safe words. Opposite-root ternary events and actual originals killed by fixed singleton coordinates are absent.

These alternatives exhaust the retained original family. If `L0` is present, suppressing the axial term still leaves its own count one. Otherwise the expression `1_V5+(1-1_V5)1_Vo` counts any axial retained owner once. Therefore, with

\[
t(y,z)=\sum_{n\in\mathcal T}1_{A_n}(y,z),
\]

one has on the whole sampled support

\[
F(y,z)\ge t(y,z)+1_{E_{\mathcal M}^c}(y,z).
\tag{CD242}
\]

This is stronger than the rectangle-only classification on `R_5 x (Z intersect B)`. It handles five-free retained nonaxial owners explicitly; they are not dropped merely because they share `I_ind` with T.

Every excluded five guard is itself a retained unit original at the selected root, independently of the ordinary cofactor. Thus

\[
E_y\subseteq Z\quad\text{for every selected cofactor }y.
\tag{CD243}
\]

No source condition `y in Y` or `y in R_5` is needed for CD243.

#### Pointwise charge and exact cancellation

Put

\[
D_T(y,z)=t(y,z)
 -1_{\{(y,z)\in E_{\mathcal M},\ \exists n\in\mathcal T:A_n(y,z)\}}.
\tag{CD244}
\]

Its value is nonnegative: inside the reached hole subtract one from a positive integer; elsewhere subtract zero. Moreover

\[
0\le D_T\le F-1\quad\text{on the whole sampled support}.
\tag{CD245}
\]

Indeed outside the hole CD242 gives `F-1>=t=D_T`; inside the reached hole it gives `F-1>=t-1=D_T`; inside the unreached hole `D_T=0` and whole coverage supplies `F-1>=0`.

All T prefixes lie inside B. Exact finite counting, actual factorization `A_n(y,z) iff C_n(y) and z in P_n`, and CD243 give

\[
\int D_T\,d\mu
 =\sum_{n\in\mathcal T}\mu(A_n)
   -\int\frac{|E_y\cap V_T(y)|}{|Z|}\,d\nu(y).
\]

Consequently the full T raw losses cancel exactly:

\[
\boxed{
\sum_{n\in\mathcal T}(u_n-\mu(A_n))
       +\int D_T\,d\mu
       =\int O_{\rm all}\,d\nu.
}
\tag{CD246}
\]

Raw prefix points outside Z remain in `u_n`; they are paid by these raw losses. They are not counted as sampled points or silently removed from CD241.

The H raw loss is exactly `s*nu(C_n)`. Its original indices are disjoint from T. Apply CD245–246 to CD240 and keep the actual45 boost as the same separate axis allowance:

\[
\boxed{
\mathfrak D_{\rm all}:=
 s\sum_{n\in\mathcal H}\nu(C_n)
 +\frac{\chi s c_{j_0}}k
 +\int O_{\rm all}\,d\nu
 \le S/k.
}
\tag{CD247}
\]

This also proves the requested unclipped full-`R_5` bound by restriction. In fact outside `R_5` a retained five-free original covers the entire five-coordinate, so `E_y` is empty and

\[
\int O_{\rm all}\,d\nu
 =\int_{R_5}O\,d\nu
 +\sum_{n\in\mathcal T}\frac{|P_n|}{|Z|}\nu(C_n\setminus R_5).
\tag{CD248}
\]

On Y, whole coverage and exclusion of H give `O_all=(q-d)/(5*rho)`. Hence `mathfrak D_all >= mathfrak D_*` from CD200. CD247 is a stronger allocation from the same CD240 decomposition; it is not an extra budget to add to CD200 or CD204.

For CD205, any fixed original matching now gives its complete sum without clipping. For the CD235 masked packet, the multiplicity proof of `F_u<=O` does not use CD234. Only `F_u<=s` uses that raw-capacity condition. Thus CD247 permits removing CD234 while retaining every original-label distinction, comparison-word mask, noncontainment hypothesis and whole-coverage condition. Separate lower bounds on the same O still cannot be added without a common pointwise multiplicity argument.

### Actual45 and two safe words

Assume `J={u,v}`, actual45 has full word v and first-five phase omega, and the complete source has `Y_u` nonempty. Then `Y_v` is empty.

Comparable-original disjointness follows from global count minimality: a compatible original proper multiple of an original modulus would be redundant. Every other high original with word v and first-five phase omega has modulus `9*5^e*m`, `e>=1`, and its whole class would lie inside actual45. Therefore none exists. This includes all deep high ordinary originals and all deeper high unit originals at that phase. It does not remove high shallow or deep originals at u, or high originals at other first-five phases.

CD223–238's two-word certificate is identically empty in this branch. A donor at u can only compare with v, where `Y_v` is empty; a high donor at v in the relevant phase does not exist. A different nonempty comparison word is not available.

Let

\[
\begin{aligned}
l(w)&=\sum_{\substack{n\in\mathcal T\\h_n\le1}}
          5^{1-e_n}1_{C_n^{\rm ord}}(w),\\
h(w)&=\sum_{\substack{n\in\mathcal T\\h_n=2,\ \operatorname{word}(n)=u}}
          5^{1-e_n}1_{C_n^{\rm ord}}(w),\\
L&=\int l\,d\lambda=L_{\rm deep},\qquad
H=\int h\,d\lambda=H_{{\rm deep},u}.
\end{aligned}
\tag{CD249}
\]

In CD249, `C_n^ord` keeps CD192's active-root convention: a ternary-inactive or opposite-root original contributes zero. The active low functions and actual prefixes are shared by both safe words. Actual45 covers all of `{v} x O x B`, so the complete retained hole at v is empty for every ordinary point. Since no relevant high T label exists there,

\[
\boxed{O_{\rm all}(v,w)=\frac{l(w)}{5\rho}}
\quad\text{for every selected }w.
\tag{CD250}
\]

This is the full ordinary-law low payment. Restriction to `R_v` would lose an additional positive term already paid by retained five-free overcount. No common-section lower bound is required.

Writing `c=c_v`, CD247 becomes

\[
\boxed{
2s\sum_{n\in\mathcal H}\nu(C_n)+s c
 +\int O_{\rm all}(u,w)\,d\lambda(w)
 +\frac{L}{5\rho}\le S.
}
\tag{CD251}
\]

The actual45 axis term and the last low term use different nonnegative pieces of CD240. The former increases the unit-axis allowance; the latter combines T slot losses and genuine covered-event multiplicity. They may therefore appear together once.

### Scalar consumer with the source variable eliminated

Put

\[
a=\lambda(Y_u),\qquad q=\lambda(R_u),\qquad
 d=d_u>0,\qquad g=5\rho s\ge1/5,\qquad
 O_u^*=\int O_{\rm all}(u,w)\,d\lambda(w).
\]

At u the depth-one unit exclusion is absent. The complete-source identity of CD190 therefore gives

\[
\sum_{j\in\{u,v\}}\sum_{n\in\mathcal H}
       \lambda(C_{n,j}^{\rm ord})\ge q-a.
\]

Here high H labels at u are still counted. The claim does not replace all H by low labels.

Complete deep service on `Y_u`, with the actual same-word hole density d, gives

\[
0\le a\le q,\qquad d a\le L+H,
\qquad 0\le H\le a_G W,
\quad a_G=\frac{1-5^{1-G}}4=\frac{A_G}{5}.
\tag{CD252}
\]

Multiply CD251 by `5*rho` and retain its nonnegative u-word excess. Since `L>=0`,

\[
5\rho S\ge5\rho O_u^*+g c+g(q-a)+[d a-H]_+.
\tag{CD253}
\]

For `g>=0,d>0,H>=0,q>=0`, direct minimization of this continuous piecewise-linear function yields

\[
\inf_{0\le a\le q}\{g(q-a)+[d a-H]_+\}
 =\min(g,d)[q-H/d]_+.
\tag{CD254}
\]

If `H>=d*q`, take `a=q`; the value is zero. Otherwise the breakpoint is `a=H/d`. Below it the slope is `-g`; above it the slope is `d-g`. The minimum is the breakpoint value when `d>=g` and the right-endpoint value when `d<=g`.

Thus the same actual family satisfies

\[
\boxed{
5\rho S\ge5\rho O_u^*+g c+\min(g,d)[q-H/d]_+
 \ge5\rho O_u^*+g c+\min(g,d)[q-a_GW/d]_+.
}
\tag{CD255}
\]

Keeping actual H is stronger. The inventory substitution uses its upper bound in the correct direction and does not assume independent attainability of source and supply extrema. A strict reverse inequality in any admissible branch would close that branch. No uniform strict inequality is asserted.

### Fixed-exception tuple consumer now charges all low load

At word u choose one fixed valid original exceptional set `X_u`, supplied by the fixed-collision theorem, before fixing any ordinary point. Retain Report850 CD208's actual second-color functions `l_c,x_(u,c),h_(u,c)`, residual hole densities `delta_c in (0,1]`, and exact actual tuple moment `Z_(u,K)`. Low and exceptional functions remain distinct, and all retained unit towers remain in `delta_c`.

For any nonempty set K of available colors, define

\[
\begin{aligned}
\delta_{\min,K}&=\min_{c\in K}\delta_c,\\
\theta_K&=\sum_{c\in K}\frac{X^*_{u,c}}{\delta_c}
             +\frac{Z_{u,K}}{\prod_{c\in K}\delta_c},\\
t_K&=\delta_{\min,K}/5.
\end{aligned}
\tag{CD256}
\]

The source-restricted exceptional integral from CD215 may replace the full `X^*` for a sharper actual quantity. Using the full `X^*` keeps `theta_K` independent of the scalar relaxation variable a.

CD215 and nonnegativity give

\[
a\le\sum_{c\in K}\frac{L_c^*}{\delta_c}+\theta_K
 \le\frac{5L}{\delta_{\min,K}}+\theta_K.
\]

The last inequality uses `L=(1/5)*sum_(all second colors) L_c^*`; colors occupied by retained unit labels remain in that full low inventory even though K uses only available colors. Consequently

\[
L\ge t_K[a-\theta_K]_+.
\tag{CD257}
\]

Combine CD257 with the same CD251, rather than adding it to CD255. Applying CD254 with `d=t_K,H=t_K*theta_K` gives

\[
\boxed{
5\rho S\ge5\rho O_u^*+g c+\min(g,t_K)[q-\theta_K]_+
 =5\rho O_u^*+g c+t_K[q-\theta_K]_+.
}
\tag{CD258}
\]

The equality uses `g>=1/5` and `delta_min<=1`. If four colors are available, at least two contain no exceptional label; choosing such K removes its exceptional term completely. It does not discard low supply. If a valid smaller X is available, use it with the same original tuple data.

Keeping all these lower bounds for the same L gives the common scalar relaxation

\[
5\rho S\ge5\rho O_u^*+g c+
\inf_{0\le a\le q}\left[
 g(q-a)+\max\left\{0,d a-H,
                  \max_K t_K(a-\theta_K)\right\}\right].
\tag{CD259}
\]

Every term in the maximum is a lower bound for the same actual L. Separate resulting lower bounds may be maximized, not added. Evaluating CD259 is a finite piecewise-linear calculation when actual data are supplied; no new scan is asserted here.

The tuple moment uses independence only under the full guarded product law. It still supplies no conditional independence on Y. CD250 is what permits the tuple's full-law low load to enter the debit without an unknown `Y_u intersect R_v` overlap. Exceptional top service and the regular tuple allowance remain payable, and the necessary strict inequality is unresolved.

### Remaining strict inequality

The two-word packet degenerates, but the all-cofactor budget preserves a new full-law low payment in the blocked word. CD255 and CD258–259 are necessary same-family inequalities. No theorem here forces their strict reverse inequality in every allowed palette, unit configuration and actual source.

Report385 §175 only disproves a local probe-to-parent-payment shortcut and is deliberately not a whole cover. Report850's 26-label zero-excess control has actual45 at a different first-five phase; it is not a counterexample to this same-omega blocked-word branch. Report853 requires whole inverse containment, common payment and legal numerical ownership; pair intersections or a fractional allocation do not supply them. None of these controls refutes the hypothetical EB1 whole-cover assumptions, and none closes unrestricted Erdős #7.

### Extremal-event identities and their positivity boundary

Under the full guarded ordinary product law, the fixed regular high
family outside X has disjoint events whenever two original cofactors
share a prime. A collection with disjoint prime supports is jointly
independent. This is Condition5 of Guo, Jerrum and Liu,
[*Uniform Sampling through the Lovász Local Lemma*, arXiv:1611.01647v4](https://arxiv.org/abs/1611.01647v4).
Their section3, equation(3), computes exact event-occurrence probabilities
by inclusion–exclusion at the actual marginals. Report387 CC12 and CD212
already provide the corresponding intersection expansion; this is reuse,
not an additional strict estimate.

The indices are original labels, including distinct originals with the
same numerical cofactor. Variables are complete guarded prime-power
coordinates, not independent digits; zero events may be removed and
unit-cofactor labels stay outside the regular family. Conditioning on Y
or R does not preserve the required product law automatically. The
paper's Theorem13 additionally assumes positive avoidance probability,
and Theorem8 conditions its output law on halting. Neither premise
follows from the intersection identity. Thus this citation supplies no
strict-closing term to add to CD247, CD255 or CD258.


### Pointwise color deficits consume the same whole-cofactor budget

Keep CD249–251's actual45 branch, the same whole covering family, the
same guarded ordinary product law lambda, and the same fixed exceptional
original set `X_u`. All functions below belong to that one actual
realization. In particular, the exceptional set is fixed before an
ordinary point is selected.

Use all five second-five colors `gamma`, including a color occupied by
a retained depth-two unit. Let `B_gamma` be the full ambient color
fiber inside the first-five phase omega, and let `E_unit` be the
complement of every retained unit tower at u. Put

\[
\delta_\gamma=
 \frac{|E_{\rm unit}\cap B_\gamma|}{|B_\gamma|}\in[0,1],
\qquad d=\frac15\sum_\gamma\delta_\gamma>0.
\tag{CD260}
\]

Thus an occupied color has `delta_gamma=0`; it is not removed from
the sums. The complete all-Mixed deletion hole at `(u,w)` is
`E_unit` when `w in R_u`, and is empty otherwise. The unit complement
and its five densities do not depend on w.

Write `R=R_u`, and let `mathsf H(w)` mean that an actual ordinary-bearing
depth-one original at phase omega is incident at u. Retain the full
two-word shallow count

\[
N(w)=\sum_{j\in\{u,v\}}\sum_{n\in\mathcal H}
             1_{C_{n,j}^{\rm ord}}(w),
\qquad
\mathsf H(w)\Longrightarrow N(w)\ge1.
\tag{CD261}
\]

A low shallow original contributes at both words. There is no
depth-one unit original at `(u,omega)`: actual5 or the applicable
root15 there would contain actual45, while actual45 itself has word v.
Consequently the complete source is `Y_u=R intersect mathsf H^c`.

Extend CD208's actual color-load functions to all five colors:
`l_gamma` is the low deep load, `x_gamma` the deep high load in
`X_u`, and `h_gamma` the deep regular high load outside `X_u`.
Every incident original contributes its actual raw color weight
`5^(2-e_n)`. Distinct originals remain separate indices even when
their numerical cofactors agree. Put `b_gamma=x_gamma+h_gamma` and
let the reached-hole fraction be

\[
r_\gamma(w)=
 \frac{|E_{(u,w)}\cap V_T(u,w)\cap B_\gamma|}{|B_\gamma|}.
\tag{CD262}
\]

The full ambient prefix union bound and whole coverage give

\[
\begin{aligned}
0&\le r_\gamma\le l_\gamma+b_\gamma,\\
w\in R&\Longrightarrow r_\gamma\le\delta_\gamma,\\
w\notin R&\Longrightarrow r_\gamma=0,\\
w\in R\cap\mathsf H^c&\Longrightarrow r_\gamma=\delta_\gamma.
\end{aligned}
\tag{CD263}
\]

The last line retains the complete source condition. Raw prefixes
outside `Z_5` remain in the loads; their allowances are already paid
by CD246's cancellation.

With `g=5*rho*s>=1/5`, define

\[
\begin{aligned}
l&=\frac15\sum_\gamma l_\gamma,&
t_b&=\frac15\sum_\gamma b_\gamma,\\
o&=5\rho O_{\rm all}(u,w)
   =\frac15\sum_\gamma(l_\gamma+b_\gamma-r_\gamma),&
P&=gN+l+o
   =gN+\frac15\sum_\gamma(2l_\gamma+b_\gamma-r_\gamma).
\end{aligned}
\tag{CD264}
\]

The normalization is exact because
`|B_gamma|=5^(G-2)` and `|Z_5|=rho*5^G`. CD250 supplies the
additional low payment l from the blocked word v. Thus CD251 is

\[
\boxed{5\rho S\ge g c_v+\int P\,d\lambda.}
\tag{CD265}
\]

For a nonnegative color-load vector b, set

\[
D_b=\frac15\sum_\gamma[\delta_\gamma-b_\gamma]_+,
\qquad
E_b=\frac15\sum_\gamma[b_\gamma-\delta_\gamma]_+.
\tag{CD266}
\]

On `R intersect mathsf H^c`, CD263 implies `l>=D_b`; on
`R intersect mathsf H`, the shallow payment is at least g. Therefore

\[
gN+l\ge1_R\min(g,D_b),
\qquad
\boxed{
5\rho S\ge g c_v+5\rho O_u^*
                  +\int_R\min(g,D_b)\,d\lambda.
}
\tag{CD267}
\]

This form leaves the actual u-word excess unspent. A second form
uses that same excess jointly with the low load:

\[
\boxed{
P\ge
\begin{cases}
E_b+\min(g,D_b),&w\in R,\\
t_b,&w\notin R.
\end{cases}}
\tag{CD268}
\]

Indeed, on `R intersect mathsf H^c`, one has
`r_gamma=delta_gamma` and
`l_gamma>=[delta_gamma-b_gamma]_+`, so

\[
2l_\gamma+b_\gamma-r_\gamma
 \ge[\delta_\gamma-b_\gamma]_+
      +[b_\gamma-\delta_\gamma]_+.
\]

On `R intersect mathsf H`, the same summand is both nonnegative
and at least `b_gamma-delta_gamma`; hence `l+o>=E_b`, while
`gN>=g`. Outside R, CD263 gives `l+o=2l+t_b>=t_b`.
These three cases prove CD268 without conditioning the ordinary law.

Since

\[
0\le D_b\le d,
\qquad t_b-d=E_b-D_b,
\qquad f_b=D_b+\min(g,D_b)-d,
\tag{CD269}
\]

the joint payment has the equivalent form

\[
P\ge t_b+1_R f_b,
\qquad
\boxed{
5\rho S\ge g c_v+\int t_b\,d\lambda+\int_R f_b\,d\lambda.
}
\tag{CD270}
\]

Here `O_u^*` is already consumed. CD270 cannot be added to CD267,
to CD255, or to another lower bound on that same excess.

### The fixed exceptions have a clipped actual price

For the regular vector h, use the same definitions `D_h,E_h,t_h,f_h`,
and put

\[
X(w)=\frac15\sum_\gamma x_\gamma(w).
\]

Adding the nonnegative exception vector gives

\[
D_h-X\le D_b\le D_h,
\qquad E_b\ge E_h,
\qquad t_b=t_h+X.
\tag{CD271}
\]

The map `z -> min(g,z)` on nonnegative z is increasing,
1-Lipschitz, and takes values in `[0,g]`. Consequently

\[
E_b+\min(g,D_b)
 \ge E_h+\min(g,D_h)-\min(g,X).
\tag{CD272}
\]

CD268 then yields

\[
P\ge t_h+1_R f_h-1_R\min(g,X),
\qquad
\boxed{
5\rho S+\int_R\min(g,X)\,d\lambda
 \ge g c_v+\int t_h\,d\lambda+\int_R f_h\,d\lambda.
}
\tag{CD273}
\]

Outside R an additional X is available and has been discarded.
No independence of the exceptions from R or from the regular events
is used.

There are at most two actual deep high exception labels. For two
such labels, let `A_i` be their actual ordinary-prefix events and
write

\[
X=a_1 1_{A_1}+a_2 1_{A_2},
\qquad a_i=5^{1-e_i}\le1/5\le g,
\qquad p_i=\lambda(A_i),\quad p_{12}=\lambda(A_1\cap A_2).
\]

The exact full-law price is

\[
\boxed{
B_X:=\int\min(g,X)\,d\lambda
 =a_1p_1+a_2p_2-[a_1+a_2-g]_+p_{12}.
}
\tag{CD274}
\]

With zero or one exception, omit the absent terms. The intersection
probability is that of the two actual cylinders under the same
guarded product law; it is not replaced by `p_1*p_2` without the
corresponding disjoint-support condition. Clipping improves the
unclipped price only when the coefficient and actual overlap in
CD274 are both positive. For `q=lambda(R)`,

\[
0\le\int_R\min(g,X)\,d\lambda\le\min(gq,B_X).
\tag{CD275}
\]

### A finite lower-tail consumer removes the unknown source association

Let `mathcal R` be the actual regular high deep original labels at u.
For a regular occurrence pattern `I subseteq mathcal R`, retain its
exact full-law probability

\[
Q_I=\lambda\!\left(\left\{w:
       \{n\in\mathcal R:w\in C_n^{\rm ord}\}=I\right\}\right).
\tag{CD276}
\]

CD212 and Report387 CC12 give these probabilities from the actual
intersection expansion: shared-prime regular events are disjoint,
and collections with disjoint ordinary-prime supports are independent
under the full guarded law. Thus the nonzero intersections use the
products of the actual event probabilities, with every original label
retained. This computation does not condition on R.

For every pattern, define

\[
\begin{aligned}
h_\gamma(I)&=
 \sum_{\substack{n\in I\\\operatorname{color}(n)=\gamma}}
                      5^{2-e_n},\\
D(I)&=\frac15\sum_\gamma[\delta_\gamma-h_\gamma(I)]_+,
\qquad t(I)=\frac15\sum_\gamma h_\gamma(I),\\
f(I)&=D(I)+\min(g,D(I))-d.
\end{aligned}
\tag{CD277}
\]

The actual joint masses
`alpha_I=lambda(R intersect {pattern=I})` obey
`0<=alpha_I<=Q_I` and `sum alpha_I=q`. Define the finite threshold value

\[
\mathcal L_q(f)=
 \sup_{\tau\in\mathbb R}
 \left\{\tau q-\sum_IQ_I[\tau-f(I)]_+\right\}.
\tag{CD278}
\]

This is the existing lower-tail fractional-knapsack quantity of
[note16 KR2](../../001-064/16-a-common-dual-test-law-for-redistributing-charged-bad-mass.md).
For its complement formulation, remove zero-mass patterns and take
weights `Q_I`, nonnegative values
`Q_I F(I)` with `F(I)=f(I)+d=D(I)+min(g,D(I))`, budget `1-q`,
and actual item variables `1-alpha_I/Q_I`. Their capacity is exactly
`1-q`, so they are feasible for the existing upper-knapsack problem.
Subtract its dual upper value from `sum Q_I F(I)` and then subtract
`d*q`. The substitution `tau=price-d` gives CD278. Prices below
`tau=-d` cannot improve the value because `f(I)>=-d` and `q>=0`.
In particular,

\[
\int_R f_h\,d\lambda=\sum_I\alpha_I f(I)
 \ge\mathcal L_q(f).
\tag{CD279}
\]

Equivalently, each threshold follows directly from
`alpha_I*f(I)>=tau*alpha_I-Q_I*[tau-f(I)]_+`.
Fractional boundary atoms belong to the relaxation. Neither CD279 nor
the knapsack optimum identifies a fractional selector with the actual
source, a new whole cover, or a legal recoloring.

Combining CD273, CD275 and CD279 gives the actual-family necessary
inequality

\[
\boxed{
5\rho S\ge g c_v+\sum_IQ_I t(I)
                 +\mathcal L_q(f)-\min(gq,B_X).
}
\tag{CD280}
\]

If only `q>=q_0` is available, retain nonnegative thresholds and use
the full exception price:

\[
\boxed{
5\rho S\ge g c_v+\sum_IQ_I t(I)-B_X
 +\sup_{\tau\ge0}
   \left\{\tau q_0-\sum_IQ_I[\tau-f(I)]_+\right\}.
}
\tag{CD281}
\]

The threshold expression is finite and piecewise linear in tau;
its breakpoints are the actual values `f(I)`, with zero included for
CD281. Keeping the full pattern distribution preserves simultaneous
color loads before relaxing their unknown association with the
five-free survivor. No conditional independence on R or Y is asserted.

The arithmetic contribution is CD268's joint consumption of the
two-word low payment and the reached-hole excess, followed by the
fixed-exception price. The event-occurrence expansion and finite
knapsack duality are existing results. To close a branch, one still
needs bounds on its actual pattern law, unit residuals, exception
intersections and source mass that force the right side of CD280 or
CD281 to exceed `5*rho*S`. No uniform strict inequality over all
admissible palettes and unit configurations is established here.

### A fixed collision cover has a uniform guarded weight cap

Keep the original family and the full literal collision graph at
`(u,omega)`, including every positive five depth and every ordinary
cofactor source. For each top original `n=9*5^{e_n}m_n`, define its
actual deep exceptional weight by

\[
\alpha_n(\lambda)=
\begin{cases}
5^{1-e_n}\lambda(C_n^{\rm ord}),&e_n\ge2,\ m_n>1,\\
0,&\text{otherwise}.
\end{cases}
\tag{CD282}
\]

Actual ternary-inactive and opposite-root events keep their zero
convention. Numerical distinctness makes `n -> (e_n,m_n)` injective.
The exceptional set below is selected from these integer labels and
the collision graph before choosing any ordinary point or guarded
law; zero probabilities are used only to check the selected set.

Report385 section172 supplies matching number at most one. Its GLC4
proof also supplies the stronger local fact that at most two originals
occupy any one literal ordinary-prime root. The latter, rather than
only the displayed aggregate bound `#{n:p|m_n}<=p`, is needed for the
triangle case. It follows there from divisor closure, DR8 and
comparable-original disjointness.

For an active ordinary prime `p>=7`, CD217 gives

\[
\eta_{p,a}\le p^{1-a}\,\overline\eta(p),
\qquad
\overline\eta(p)=\frac{p-1}{p(p-3)}.
\tag{CD283}
\]

The function `overline eta` decreases for `p>=7`: for `7<=p<=r`,
its cross-multiplied numerator difference is
`(r-p)(pr-p-r+3)>=0`. In particular
`overline eta(7)=3/14`, `overline eta(11)=5/44` and
`overline eta(13)=6/65`. Every remaining active factor is below one,
so discarding other prime factors gives a valid upper bound on an
actual event probability. An inactive original contributes zero.

The graph classification gives a fixed choice `X_u` with

\[
\boxed{
|X_u|\le2,\qquad X_u\text{ meets every collision edge},\qquad
\sum_{n\in X_u}\alpha_n(\lambda)\le\frac3{350}
}
\tag{CD284}
\]

simultaneously for every guarded law satisfying CD217. Isolated
vertices are omitted. To see the uniformity, fix an ordering of
original labels for tie breaking and use the following choices.

If there is no edge, choose the empty set. If there is a single edge
and a shallow endpoint, select such an endpoint. Otherwise both
endpoints are deep. They cannot both have `e=2,m=p` prime: a collision
would force the same p and the same numerical modulus 225p. Select a
nonprimitive endpoint using its `(e,m)`. At depth at least three its
weight is at most `overline eta(7)/25=3/350`. At depth two, a prime-power
cofactor `p^a`, `a>=2`, gives at most
`overline eta(7)/(5*7)=3/490`; at least two distinct ordinary primes
give at most `overline eta(7)overline eta(11)/5=3/616`.

For a star with at least two leaves, select its center. Two different
center-leaf edges have different witness primes; otherwise the leaves
would share the center's literal root and would be adjacent. The
center therefore has at least two distinct ordinary prime factors,
so its deep active weight is at most 3/616.

For a triangle, choose a witness prime for each edge by a fixed rule,
such as the smallest witness prime. These three witnesses are
pairwise distinct: equality for two incident edges would put all
three originals at one literal prime/root, contrary to GLC4's local
cap. Select the two endpoints of the edge with largest witness r.
They meet every edge. Writing p,q for the other two witnesses, with
`p<q`, gives `p>=7,q>=11,r>=13`, and therefore

\[
\sum_{n\in X_u}\alpha_n
\le\frac{\overline\eta(r)}5
       \bigl(\overline\eta(p)+\overline\eta(q)\bigr)
\le\frac{303}{50050}<\frac3{350}.
\]

A shallow or inactive selected endpoint only decreases these sums.
None of the cases assumes that the complete ordinary cylinders have
a common point, and none uses the probability law to choose X.

For this same fixed `X_u`, the all-color normalization in CD260–274
gives `integral X d lambda=sum_{n in X_u} alpha_n`. Thus

\[
B_X\le\int X\,d\lambda\le\frac3{350},
\qquad
\int_R\min(g,X)\,d\lambda
 \le\min\left(gq,\frac3{350}\right).
\tag{CD285}
\]

Only the actual deep-high part of `X_u` enters this identity; no
shallow or low load is added. Recompute the regular set, its pattern
probabilities `Q_I`, and the functions `h_gamma(I),t(I),f(I)` using
this same `X_u`. A change of exceptional set changes those data, so
one cannot minimize the scalar exception price while retaining the
pattern law of a different choice.

CD280 now yields the safe necessary inequality

\[
\boxed{
5\rho S\ge g c_v+\sum_IQ_I t(I)+\mathcal L_q(f)
                 -\min\left(gq,\frac3{350}\right).
}
\tag{CD286}
\]

If only `q>=q_0` is available, CD281 instead gives

\[
\boxed{
5\rho S\ge g c_v+\sum_IQ_I t(I)-\frac3{350}
 +\sup_{\tau\ge0}
   \left\{\tau q_0-\sum_IQ_I[\tau-f(I)]_+\right\}.
}
\tag{CD287}
\]

These bounds retain the same actual family, residual colors, regular
pattern law and source mass. They do not assert independence of R
from exceptions or regular occurrences. The joint-use budget has
already consumed the actual excess, so it cannot be added to CD267's
unspent-excess inequality.

The existing fixed-collision Lean theorem supplies a fixed set of at
most two labels. The literal prime/root capacity also has a
[general-height Lean proof](https://github.com/the-omega-institute/trureturing/blob/9ca162aa5fb65ba6dfe07c504db62cb685a6c6df/D5/S3/Arith/Covering/PrimeRootCapacity.lean):
under the full same-count modulus-sum minimum, three top originals at
one specified ordinary-prime root admit a cheaper three-class
replacement. Its height-two application retains the existing
collisionTop predicate. The weighted choice above still requires the
graph classification, original numerical injectivity and the actual
guard-law source; their combined weighted-selection bridge remains
an ordinary mathematical argument. Separate finite checks of guard
monotonicity, the rational constants and the scalar penalty replacement
do not verify that bridge. No uniform strict contradiction for the
shared-five branch follows from CD286 or CD287 without further control
of their actual pattern data.

### The unit inventory determines which tail threshold is available

Keep the actual45 branch and its same fixed original family and law.
Let `epsilon` indicate that75 has the selected ternary root and
first-five phase omega, and let `beta` indicate that225 has word u
and first-five phase omega. Actual25 is always present there.
Let `ell_U` be the deeper pure-five and root-three guard union outside
the full25 and active75 colors, let `kappa_U` be its overlap with
the full active225 color, and let `h_U` be the deeper high-unit union
outside all these guards and full colors. Normalize these actual
unions by the same first-five fiber. Then

\[
\begin{aligned}
g&=\frac{1+\epsilon}{5}+\ell_U,\\
d&=\frac{4-\epsilon-\beta}{5}
       -\ell_U+\kappa_U-h_U,\\
d-g&=\frac{3-2\epsilon-\beta}{5}
       -2\ell_U+\kappa_U-h_U.
\end{aligned}
\tag{CD288}
\]

Here `0<=ell_U<=2T_G`, `0<=h_U<=T_G`,
`0<=kappa_U<=ell_U`, and `kappa_U=0` if `beta=0`, where
`T_G=sum_(e=3..G)5^(1-e)=(1-5^(2-G))/20`.
These retain possible low/high-unit overlap; the three variables
are not independently chosen maxima.

If75 is inactive, these bounds give `d>g`. If75 and225 are both
active, CD288 gives

\[
d-g=-2\ell_U+\kappa_U-h_U\le-\ell_U-h_U\le0.
\tag{CD289}
\]

Equality in this case requires `ell_U=h_U=0`. When75 is active
and225 inactive, the exact test is
`d>=g iff 2ell_U+h_U<=1/5`; it holds for `G<=3` from the tail
inventory, while larger heights retain the actual sign. Thus the
total-load threshold `(d-g)_+` is identically zero throughout the
two-active-unit branch, not merely at an extreme capacity point.

### Zero threshold retains a color-matching obligation

Assume `d<=g`, and keep the same fixed exception set used to define
the regular high vector h. Define its clipped color service by

\[
C_h(w)=\frac15\sum_\gamma
                  \min(\delta_\gamma,h_\gamma(w)).
\tag{CD290}
\]

All five colors remain in this sum. Since `0<=D_h<=d<=g`, the
source-side joint-payment function in CD268 is exactly

\[
\begin{aligned}
\Phi_\delta(h)
  &:=E_h+D_h
    =\frac15\sum_\gamma|\delta_\gamma-h_\gamma|\\
  &=d+t_h-2C_h,\qquad
f_h=d-2C_h.
\end{aligned}
\tag{CD291}
\]

It measures color mismatch, including oversupply in a color whose
hole is already filled. Equal total demand and supply do not make
this quantity zero unless their color vectors agree.

The exception payment can be clipped at d in this branch.
Indeed `D_h-D_b<=min(d,X)` and `E_b>=E_h`, so
`Phi_delta(b)>=Phi_delta(h)-min(d,X)`. Consequently

\[
\boxed{
5\rho S\ge g c_v+\mathbb E t_h+dq
                  -2\mathbb E(1_R C_h)-K_{d,R},
\qquad
K_{d,R}:=\mathbb E[1_R\min(d,X)]
       \le\min(dq,3/350).
}
\tag{CD292}
\]

The last bound uses the same weighted fixed exception set as its
regular vector h. This is one exception payment and one use of the
original excess. Neither can be added again.

For the same exact regular-pattern probabilities `Q_I`, let

\[
\mathcal U_q(C)=
 \inf_{\tau\ge0}
 \left\{\tau q+\sum_IQ_I[C_h(I)-\tau]_+\right\}.
\tag{CD293}
\]

Existing finite knapsack duality gives
`E(1_R C_h)<=U_q(C)` by applying its box-and-capacity bound to the
actual masses `alpha_I<=Q_I`, `sum alpha_I=q`. Thus a necessary
inequality is

\[
\boxed{
5\rho S\ge g c_v+\sum_IQ_I t_h(I)+dq
                    -2\mathcal U_q(C)-\min(dq,3/350).
}
\tag{CD294}
\]

This is CD280's finite-distribution consumer expressed in the
`d<=g` variables, with the sharper exception clipping. Its optimizing
selector is a relaxation, not an asserted realization of R.

Replacing the colors by total load uses only `C_h<=t_h` and gives
the weaker debit `g c_v+dq-E t_h-K_(d,R)`. The corresponding
stop-loss threshold is zero, so its expectation is exactly the
first moment. A comparison that preserves only the total-load law
cannot recover the missing clipped color service.

### Equal total-load laws can have different color mismatch

The following finite congruence control keeps the unit hole, the
ordinary product law, the two regular event supports and their
complete total-load distribution fixed. It compares the function
`Phi_delta` in CD291. It is not a whole cover or a claim that a
common low-row completion realizes either debit.

Use `G=3`, actual3=`[0]_3`, actual9=`[1]_9`, safe words
`u=4,v=7`, and `omega=1`. Take this complete unit inventory; every
entry is an actual residue class:

| Five depth | Pure-five unit | Root-three unit | High unit |
| --- | --- | --- | --- |
| 1 | `[0]_5` | `[7]_15` | `[16]_45` |
| 2 | `[1]_25` | `[31]_75` | `[211]_225` |
| 3 | `[16]_125` | `[271]_375` | `[166]_1125` |

The25,75,225 units occupy colors0,1,2. In color3, the125 and1125
prefixes occupy different third-five children. The375 prefix occupies
one child of color4. Direct finite counting gives

\[
(\delta_0,\ldots,\delta_4)=(0,0,0,3/5,4/5),
\quad g=12/25,\quad d=7/25,\quad \rho=63/125.
\tag{CD295}
\]

Add the ordinary guards `[0]_7,[1]_21,[0]_11,[1]_33`.
At the selected ternary root, the full guarded ordinary law is uniform
on `Z_7={2,3,4,5,6}` times `Z_11={2,3,...,10}`.
For both regular originals take ordinary literal root2 and word u.
Their two color placements are

| Placement | Modulus1575=`225*7` | Modulus2475=`225*11` |
| --- | --- | --- |
| Same color | `[1066]_1575`, color3 | `[2191]_2475`, color3 |
| Split colors | `[1066]_1575`, color3 | `[1696]_2475`, color4 |

Each row has first-five phase omega. The ordinary events are
`A_7={z_7=2}` and `A_11={z_11=2}`, with probabilities `1/5`, `1/9`
and joint probability `1/45`. They have disjoint prime supports,
so the displayed two-label collision graph has no edge and admits
`X=empty`. This last assertion concerns this displayed graph; it
does not assign an empty exceptional set to an unspecified whole
cover containing other originals.

Both partial families have distinct odd nonunit labels, no27-divisible
label, disjoint classes for every comparable numerical pair, and a
private residue for every listed class. The full period is86625.
They leave21696 and21688 residues uncovered, respectively.
These noncoverage counts are part of the control's boundary.

Under the same complete ordinary product law, the occurrence table is

| Regular occurrence | Probability | Total load t in both placements | `Phi_delta`, same color | `Phi_delta`, split colors |
| --- | --- | --- | --- | --- |
| Neither | `32/45` | `0` | `7/25` | `7/25` |
| Only7 | `8/45` | `1/5` | `6/25` | `6/25` |
| Only11 | `4/45` | `1/5` | `6/25` | `4/25` |
| Both | `1/45` | `2/5` | `11/25` | `3/25` |

In particular,

\[
\begin{aligned}
\operatorname{Law}(t_{\rm same})
 &=\operatorname{Law}(t_{\rm split}),\\
\mathbb E\Phi_{\rm same}&=307/1125,
\qquad \mathbb E\Phi_{\rm split}=291/1125,\\
\mathbb E C_{\rm same}&=39/1125,
\qquad \mathbb E C_{\rm split}=47/1125.
\end{aligned}
\tag{CD296}
\]

Thus the scalar law loses a color distinction even when the displayed
exception load is zero. The units and ordinary guards are unchanged;
the2475 class changes its second-five color. No low load l is supplied
to fill the remaining hole, and the whole-coverage implication of
CD263 is not asserted for these partial families. Their computed
`Phi_delta` values therefore do not claim an attained common budget
or a recoloring that preserves coverage.

The remaining quantitative target in the zero-threshold branch is
an upper bound on `E(1_R C_h)` that retains the complete five-free
survivor and the same original supplier colors. One may bound its
full colored upper quantile as in CD293, or prove an additional
restriction on its intersection with that actual R. A total-load
tail bound or a smaller scalar exception allowance alone does not
identify this joint quantity. No strict inequality excluding all
admissible actual-source configurations is established by this control.


### Actual high five-free axes restrict the colored source capacity

Keep CD288–296's same actual original family, word u, first-five phase,
fixed weighted exceptional set, regular originals, full guarded ordinary
product law lambda and complete five-free survivor R. Assume d<=g and
write C=C_h. The source and supplier colors remain fixed throughout.

For each ordinary prime p, the coordinate law lambda_p already excludes
every actual pure p-power prefix and every applicable root-three
3*p-power prefix. These low guards are not charged again. Let V_(p,u)
be the union of the ordinary prefixes of all **actual** high five-free
originals 9*p^a at word u, retaining every actual exponent a. No absent
or differently owned label enters this union. Define

\[
K_p=Z_p\setminus V_{p,u},\qquad
\kappa_p=\lambda_p(K_p),\qquad
K=\prod_pK_p=A_u^c,\qquad
\kappa=\lambda(K)=\prod_p\kappa_p=P_u.
\tag{CD297}
\]

Thus R is a subset of K. This is an additional exclusion by actual high
five-free axes, not a repetition of the already imposed Z_p. If q>0,
every kappa_p is positive. If kappa=0, then q=0 and the restricted
service integral is zero; the normalized formulas below are needed
only when kappa>0.

A regular supplier n=9*5^e*m with v_p(m)=b is numerically divisible by
an actual axis9*p^a whenever a<=b. Comparable-original disjointness
then makes their prefixes disjoint at u. An axis with a>b is not a
divisor of n: its deeper prefix must still be intersected explicitly
with the supplier's prefix. First-p roots alone cannot replace these
full coordinate masks.

For the exact regular occurrence patterns Omega_I in CD276, put

\[
Q_I^{\rm ax}=\lambda(K\cap\Omega_I),\qquad
\alpha_I=\lambda(R\cap\Omega_I).
\]

They satisfy

\[
0\le\alpha_I\le Q_I^{\rm ax}\le Q_I,\qquad
\sum_I\alpha_I=q,\qquad \sum_IQ_I^{\rm ax}=\kappa.
\tag{CD298}
\]

The same finite upper-knapsack bound therefore gives

\[
\begin{aligned}
\mathbb E(1_R C)
 &\le\mathcal U_q^{\rm ax}(C)\\
 &:=\inf_{\tau\ge0}
       \left\{\tau q+\sum_IQ_I^{\rm ax}[C(I)-\tau]_+\right\}
 \le\mathcal U_q(C).
\end{aligned}
\tag{CD299}
\]

Masked capacities are subprobabilities. Their sum need not be one;
the actual alpha is feasible because q<=kappa. Thus CD294 strengthens
to the same-family necessary inequality

\[
\boxed{
5\rho S\ge gc_v+\mathbb E t_h+dq
             -2\mathcal U_q^{\rm ax}(C_h)-\min(dq,3/350).
}
\tag{CD300}
\]

This replaces one upper bound for the same restricted service integral.
The original excess and the fixed exception allowance are each used
once; CD300 is not a further term to add to CD294.

### Exact masked intersections retain all ordinary prefixes

For kappa>0, define the explicit auxiliary product law
`lambda^ax=product_p (lambda_p restricted to K_p)/kappa_p`.
It satisfies `lambda(K intersect E)=kappa*lambda^ax(E)`.
Let H_(i,p) be regular original i's full p-power prefix and set

\[
r_i^{\rm ax}=\prod_{p\mid m_i}
       \frac{\lambda_p(K_p\cap H_{i,p})}{\kappa_p}.
\]

Restriction preserves the empty intersections of regular originals
sharing an ordinary prime. Originals with disjoint ordinary supports
remain independent under this explicit auxiliary product law. Hence

\[
\begin{aligned}
M^{\rm ax}(T)
 &:=\lambda\left(K\cap\bigcap_{i\in T}A_i\right)\\
 &=\begin{cases}
   \kappa\prod_{i\in T}r_i^{\rm ax},
        &m_i\ (i\in T)\text{ pairwise coprime},\\
   0,&\text{otherwise},
   \end{cases}\\
Q_I^{\rm ax}
 &=\sum_{J\subseteq\mathcal R\setminus I}
                   (-1)^{|J|}M^{\rm ax}(I\cup J).
\end{aligned}
\tag{CD301}
\]

Here M^ax(empty)=kappa. This is the existing extremal-event
intersection expansion applied on K. It asserts no independence
after conditioning on R, which also excludes actual low and nonaxial
five-free originals.

An exact block version may include additional actual low or nonaxial
five-free unions: partition the prime coordinates into disjoint blocks
and remove a specified actual union inside each block. The resulting
product mask still contains R. Its tuple intersections factor across
blocks as `product_B lambda_B(K_B intersect intersection_i H_(i,B))`.
They need not factor between different primes within a block; the
per-original product in CD301 must not be reused there without proof.

### Colored service on an excluded axis gives a strict comparison

Let tau_* minimize the unmasked finite expression U_q(C). A minimizer
exists among zero and the finitely many C(I). Evaluating the masked
expression at this same threshold gives the correctly directed bound

\[
\boxed{
\mathcal U_q(C)-\mathcal U_q^{\rm ax}(C)
 \ge\sum_I(Q_I-Q_I^{\rm ax})[C(I)-\tau_*]_+
 =\mathbb E\bigl[1_{K^c}(C-\tau_*)_+\bigr].
}
\tag{CD302}
\]

Positive colored tail on an actually excluded axis therefore proves a
strict gain in this comparison. It has not been shown to occur in every
admissible whole-cover configuration.

For a concrete sufficient source of leakage, suppose9*p is actually
present at u. Let B_p be its literal p-root event and
`b_p=lambda(B_p)`. Remove from h every supplier whose cofactor contains
p, obtaining `h^(-p)`. All removed suppliers vanish on B_p by comparable
original disjointness; all remaining suppliers depend on other prime
coordinates. The full product law, before conditioning on R, gives

\[
\mathbb E\bigl[1_{B_p}(C_h-\tau)_+\bigr]
 =b_p\,\mathbb E\bigl[(C_{h^{(-p)}}-\tau)_+\bigr],
 \qquad\tau\ge0.
\tag{CD303}
\]

Since B_p is a subset of K^c, this bounds the right side of CD302
from below at tau_*. For example, an actual supplier i with p not
in its cofactor gives the lower bound
`b_p*lambda(A_i)*[min(delta_color(i),5^(2-e_i))/5-tau_*]_+`.
CD303 requires that actual shallow high axis. It does not infer9*p
from a deeper axis or replace all higher prefixes by their roots.
Conversely, divisor disjointness can concentrate a supplier on K;
it supplies no general negative association between R and C_h.

### A strict masked comparison on one partial arithmetic family

Use CD295's unit inventory and the split-color regular originals
`[1066]_1575` and `[1696]_2475`, with u=4, v=7 and omega=1.
Retain `[0]_7,[1]_21,[0]_11,[1]_33`, and add the ordinary guards
`[0]_13,[1]_39` and the high five-free axis `[67]_117`.
Its full word is4 and its literal13-root is2.

The complete guarded law is uniform on
`{2,...,6} times {2,...,10} times {2,...,12}`. All five-free
originals of this displayed partial family are specified; at word4,
their complete survivor is exactly
`R=K={z_13!=2}`, so q=10/11. The two suppliers depend only on7 and11,
so R is independent of them in this **particular** configuration.
This is the reason this example is simple to evaluate, not an
independence premise for the general consumer.

The residual vector, d and g remain
`(0,0,0,3/5,4/5)`, `7/25`, and `12/25`. With
`A_7={z_7=2}` and `A_11={z_11=2}`,
`C=(3*1_(A_7)+4*1_(A_11))/25`.
For neither, only7, only11 and both, Q is respectively
`32/45,8/45,4/45,1/45`, while `Q^ax=(10/11)Q`.
Exact finite evaluation gives

\[
\begin{aligned}
\mathcal U_q(C)&=\mathbb EC=47/1125,\\
\mathcal U_q^{\rm ax}(C)&=\mathbb E(1_RC)=94/2475,\\
\mathcal U_q(C)-\mathcal U_q^{\rm ax}(C)&=47/12375>0.
\end{aligned}
\tag{CD304}
\]

The lower-bound functional in CD300 consequently improves by
94/12375. No attained whole-cover budget is claimed.

The20 classes have distinct odd nonunit moduli, no27-divisible label,
disjoint classes for every comparable numerical pair, and a private
residue for every listed class. Their period is1126125 and they leave
252970 residues uncovered. The displayed two-supplier collision graph
is edgeless and allows X=empty for that graph only. This family is not
a cover, a global minimum, a complete divisor-closed inventory, or a
verification of the global shared-prime condition. Its role is solely
to show that the actual-axis capacity comparison can be strict.

### The axis mask also has a joint numerical-inventory consumer

Let A be the finite active ordinary palette, with CD172's prefix caps
`g_p=1/(p-3)`. Omit zero-probability originals. For each actual regular
supplier i, let S_i be its nonempty ordinary support, e_i its five depth,
`w_i=5^(2-e_i)`, `a_i=w_i/5`, and `p_i=lambda(A_i)`. Write
`c_i=min(delta_color(i),w_i)/5` and
`kappa_out(S)=product_(p in A minus S) kappa_p`.

Since A_i depends only on S_i, full-law independence across this support
and its complement gives

\[
\begin{aligned}
\lambda(R\cap A_i)
 &\le\lambda(K\cap A_i)\\
 &=\kappa_{\rm out}(S_i)
       \prod_{p\in S_i}\lambda_p(K_p\cap H_{i,p})\\
 &\le\kappa_{\rm out}(S_i)\,p_i.
\end{aligned}
\tag{CD305}
\]

Every actual higher axis prefix remains in the middle expression.
Dropping only its support-interior intersection weakens the bound;
no shallow axis or exponent divisibility is assumed here.
The elementary clipping inequality
`min(delta,sum z_i)<=sum min(delta,z_i)` gives

\[
\boxed{
\mathbb E t_h-2\mathbb E(1_R C_h)
 \ge\sum_i p_i\bigl[a_i-2c_i\kappa_{\rm out}(S_i)\bigr].
}
\tag{CD306}
\]

Both terms retain the same actual p_i. In particular, positive
coefficients may be discarded as nonnegative debit; numerical upper
caps may replace event probabilities only for the negative coefficients.

Put `delta_max=max_gamma delta_gamma`,
`r_e=min(1,delta_max/5^(2-e))`, and define

\[
T_{\rm ax}=\sum_{e=2}^{G}5^{1-e}
       \sum_{\varnothing\ne S\subseteq A}
         [2r_e\kappa_{\rm out}(S)-1]_+
                  \prod_{p\in S}g_p.
\tag{CD307}
\]

At fixed depth e and exact support S, numerical distinctness and the
full guarded prefix bounds give
`sum_(i:e_i=e,S_i=S) p_i<=product_(p in S)g_p`, and `c_i/a_i<=r_e`.
Applying these caps to the negative terms of CD306 yields

\[
\mathbb E t_h-2\mathbb E(1_R C_h)\ge-T_{\rm ax},\qquad
\boxed{5\rho S\ge gc_v+dq-T_{\rm ax}-\min(dq,3/350).}
\tag{CD308}
\]

This is another evaluation of the same CD292 debit. It neither adds
an excess charge nor changes the fixed exceptional set. Enlarging the
regular numerical inventory to all allowed slots only weakens the
lower bound. With `a_G=sum_(e=2..G)5^(1-e)`, one may further use

\[
T_{\rm ax}\le a_G
  \sum_{\varnothing\ne S\subseteq A}
       [2\kappa_{\rm out}(S)-1]_+\prod_{p\in S}g_p.
\tag{CD309}
\]

When every kappa_p=1, this last expression is a_G*W. An actual outside
axis can reduce it; a term vanishes if its outside-axis survival
probability is at most1/2. These observations compare relaxations.
The whole-cover assumptions have not been shown here to force enough
reduction in every remaining branch.

### A finite colored comparison keeps total load and service together

A separate evaluation of the same debit retains color saturation among
regular depth-two single-prime suppliers. Let h^0 consist of exactly
those actual regular suppliers with e=2 and ordinary cofactor a power
of one prime. Write h=h^0+h^1 and
`t_0=(1/5)sum h^0_gamma`,
`C_0=(1/5)sum min(delta_gamma,h^0_gamma)`,
`t_1=(1/5)sum h^1_gamma`.
Then `0<=C_h-C_0<=t_1` and `t_h=t_0+t_1`, so

\[
\begin{aligned}
\mathbb E t_h-2\mathbb E(1_R C_h)
 &\ge\mathbb E t_0-2\mathbb E(1_R C_0)-\mathbb E t_1,\\
\mathbb E t_1&\le H_{\rm tail}:=T_G B+a_G D,\\
T_G&=\sum_{e=3}^{G}5^{1-e}=(1-5^{2-G})/20,\\
B&=\sum_{p\in A}g_p,\qquad
D=\prod_{p\in A}(1+g_p)-1-B.
\end{aligned}
\tag{CD310}
\]

The remainder groups are disjoint: single-prime labels at e>=3 and
multiprime labels at e>=2. They are paid once, while the fixed exceptions
remain outside h and keep their existing one payment.

For each p and color gamma, let x_(p,gamma) be the full-law probability
that a regular depth-two p-power label of that color occurs. Regular
shared-prime disjointness, including unequal ordinary exponents, gives

\[
x_{p,\gamma}\ge0,\qquad \sum_\gamma x_{p,\gamma}\le g_p,
\qquad
C_0=\frac15\sum_\gamma\delta_\gamma
                   1_{\{\text{some prime chooses }\gamma\}}.
\tag{CD311}
\]

The per-prime categorical variables are independent under the full
product law. This still asserts no independence on R. The last equality
uses the depth-two raw load1 and `delta_gamma<=1`.

For every nonnegative threshold tau, the actual mass-q selector obeys

\[
\mathbb E_x t_0-2\mathbb E(1_R C_0)
 \ge F_x(\tau)
 :=\mathbb E_x t_0-2\tau q-2\mathbb E_x(C_0-\tau)_+.
\tag{CD312}
\]

Both expectations use the same categorical law x. With every other
prime fixed, F_x(tau) is affine in the p-category vector. The successive
simplex minimization already used in CD176 therefore gives
`min_x F_x(tau)=min_f F_f(tau)`, where f sends each prime either to
an omitted symbol or to one of the five colors. A nonomitted prime
fires independently with probability g_p in its designated color.
An omitted prime never fires. Omission is essential: the positive
load term can make unused capacity preferable. These vertices are
comparison laws, not asserted realizations of original residue classes.

For such f let `C_f=(1/5)sum_gamma delta_gamma*1{some active prime
is assigned gamma}` and put

\[
\begin{aligned}
J(q,\delta,A)
 &=\sup_{0\le\tau\le d}\min_f
       \left\{\frac15\sum_{p:f(p)\ne\bot}g_p
             -2\tau q-2\mathbb E(C_f-\tau)_+\right\},\\
5\rho S
 &\ge gc_v+dq+J(q,\delta,A)
                -H_{\rm tail}-\min(dq,3/350).
\end{aligned}
\tag{CD313}
\]

Since C_f<=d and q>=0, thresholds above d cannot improve this
supremum. The q in CD313 remains the same actual source mass as in
CD292 and the common-axis constraints. If only a range for q is
available, the entire right side must be minimized over that same
range. A substitution `q>=q_0` into a coefficient `d-2tau` requires
checking its sign.

The necessary minimax direction is only

\[
\min_x\{\mathbb E_x t_0-2\mathcal U_q(C_0)\}
 =\min_x\sup_\tau F_x(\tau)
 \ge\sup_\tau\min_xF_x(\tau).
\tag{CD314}
\]

No equality after exchanging minimum and supremum is claimed. The
right side admits mixtures of vertex laws and can weaken the product-law
optimization. Complete actual-pattern data retain more information.
CD313 does not independently minimize E t and maximize C from different
source configurations.

### The legal minimax relaxation can retain a strict color gain

A finite categorical control uses
`delta=(0,0,0,3/5,4/5)` and the two probability caps `(1/5,1/9)`
from CD296. These caps describe this two-event control; they do not
replace the general prime-power caps g_p. Enumerating all omitted/color
vertices and the exact rational threshold-envelope intersections gives

\[
\begin{array}{c|c|c|c}
q&J_{\rm color}&J_{\rm scalar}&J_{\rm color}-J_{\rm scalar}\\\hline
1/5&-3/125&-1/25&2/125\\
1/4&-11/400&-99/2000&11/500\\
1/2&-34/1125&-64/1125&2/75
\end{array}
\tag{CD315}
\]

The scalar comparison replaces C_0 by `min(d,t_0)`, which can only
increase its positive-part term and weaken the lower bound. All five
colors can be included in the vertex enumeration; replacing a
zero-demand color by omission preserves C_0 and decreases E t_0.

Within this categorical relaxation, assign both primes to the color
of demand4/5 and take their event probabilities respectively
`(1/5,0)`, `(1/5,1/16)`, and `(1/5,1/9)`. Each is feasible under
the same caps and its exact `E t_0-2U_q(C_0)` equals the corresponding
colored value. The lower bound and these feasible relaxed laws therefore
show no minimax loss in these three controls. They are not constructed
congruence families or actual five-free sources, and the table excludes
no new arithmetic palette.

CD299 and CD312 reuse finite knapsack; CD301 reuses the extremal-event
expansion; the vertex reduction reuses separate affinity on simplexes.
Their arithmetic inputs are the actual high-axis mask, original support
and depth inventory, and regular single-prime extraction. Those bridges
and the complete strict whole-cover consumer remain ordinary mathematical
arguments here. The exact finite controls establish the displayed
rational comparisons and partial-family counts, not Lean verification
of the whole chain or a completed Erdős #7 exclusion.

Further branch exclusion requires actual whole-cover information forcing
suitable high axes at u, or otherwise restricting the same masked colored
pattern data, in a configuration not already excluded by CD255 and the
common-axis budget. No such uniformly strict reverse inequality is
established above.

### The actual45 word restricts the old axis envelope

Keep the same actual45 branch and original unit and ordinary-axis
ownership as CD297–315. Write
`P_u=product_p(1-x_(p,u))=product_p kappa_p` and
`P_v=product_p(1-x_(p,v))`. These are the same ordinary high-axis
complements used by the source mask, not independently selected
products. Let gamma be the actual45 cylinder mass in the guarded
five-coordinate law, and retain CD189's
`s=1/(5rho)-gamma`, `g=5rho*s`.

The full high-five tower union at v contains that actual45 cylinder,
so `x_(5,v)>=gamma`, even if other unit cylinders also occur. CD199
adds s to this same v-coordinate. Consequently its boosted vector
satisfies

\[
z_{5,v}=x_{5,v}+s\ge\gamma+s
     =a_{45}:=\frac1{5\rho},\qquad
z_{5,u}+z_{5,v}\le r,\qquad a_{45}\le r.
\tag{CD316}
\]

The sum cap is the same original shared-axis cap; the added s is the
actual45 raw-slot correction already used in CD199. The mandatory
coordinate is v because this original45 is at v. It cannot be moved
to u when optimizing the remaining ordinary-axis data.

Keep the actual ordinary Pu,Pv and actual low mass ell. Since
`ell<=Lbar<=P<=P_u,P_v`, both coefficients in

\[
G_\ell(z)
 =2-P_u-P_v+z_{5,u}(P_u-\ell)+z_{5,v}(P_v-\ell)
\]

are nonnegative. After reserving a45 at v, place at most r-a45 in
the larger coefficient. This gives

\[
\begin{aligned}
G_\ell(z)&\le2-M_{45}-r\ell,\\
M_{45}&:=P_u+P_v-a_{45}P_v
                      -(r-a_{45})\max(P_u,P_v),\\
M_{\rm pair}&:=P_u+P_v-r\max(P_u,P_v),\\
M_{45}&=M_{\rm pair}+a_{45}[P_u-P_v]_+.
\end{aligned}
\tag{CD317}
\]

The unconstrained ordinary/shared simplex envelope in CD176 already
gives `M_pair>=M_2(r)`. Thus the nonnegative remaining envelope slack
is

\[
\begin{aligned}
\Delta_{45}&:=M_{45}-M_2(r)\ge0,\\
5\rho\Delta_{45}
 &=5\rho\bigl(M_{\rm pair}-M_2(r)\bigr)+[P_u-P_v]_+.
\end{aligned}
\tag{CD318}
\]

This slack is determined by the same actual ordinary-axis allocation
as kappa in CD297 and CD307. It may not be minimized at one axis
allocation while the service mask is evaluated at another.

### The original decomposition retains the new envelope slack once

In CD199, adding s to the actual v-coordinate gave the exact left side
`Bmajorant-1+s*c_v/2`, before the shared/ordinary upper envelope was
used. Replacing only that upper-envelope step by CD317 yields

\[
\mathcal B-1+\frac{s c_v}{2}
       \le\frac{S-\Delta_{45}}2.
\tag{CD319}
\]

The original raw-slot loss and overcount decomposition is unchanged.
Therefore CD247, CD251 and their common-budget consumers may use
`S-Delta45` in place of S. For example CD300 becomes

\[
\boxed{
\begin{aligned}
5\rho S\ge{}&gc_v+\mathbb E t_h+dq
        -2\mathcal U_q^{\rm ax}(C_h)-\min(dq,3/350)\\
 &+5\rho\bigl(M_{\rm pair}-M_2(r)\bigr)+[P_u-P_v]_+.
\end{aligned}}
\tag{CD320}
\]

The term g*c_v remains the one actual45 boost payment. The added
quantity is the slack in the upper envelope of that **same boosted
axis vector**; it is not a second boost or another `r->r-s` deduction.
The original excess and exceptional allowance are still consumed once.
The same substitution applies to CD308 or CD313, retaining the actual
axis allocation in all the terms used together.

### Little exclusion at u has an explicit envelope cost

The actual two-word axis allocation obeys, for every p,

\[
x_{p,u}+x_{p,v}\le g_p,\qquad
\kappa_p=1-x_{p,u},\qquad\eta_p=1-x_{p,v},\qquad
\eta_p\ge2-g_p-\kappa_p.
\tag{CD321}
\]

In particular `P_v>=product_p(2-g_p-kappa_p)`. Source constraints
retain these same products:
`q<=P_u`, `c_v<=P_v`,
`q>=[P_u-Lbar-D]_+` and `c_v>=[P_v-Lbar]_+`.
The common-axis lower bound for `c_v+q` also remains available.
These are restrictions on one actual allocation, not certificates
that their bounds are simultaneously attainable.

A simple consequence already prevents the zero-mask endpoint from
using the old unconstrained envelope freely. Since the partition
placing all ordinary axes at v is admissible for the old M2 minimum,
`M_2(r)<=1-r+P`. Also `0<=a45<=r<=1/2` and `P_u,P_v>=P`.
For fixed P_u the function M45 is increasing in P_v: its two slopes
are `1-a45` and `1-r`. Thus
`M45>=(1-r+a45)P_u+(1-a45)P`, which gives

\[
\begin{aligned}
\Delta_{45}
 &\ge\bigl[a_{45}(1-P)
              -(1-r+a_{45})(1-P_u)\bigr]_+,\\
5\rho\Delta_{45}
 &\ge\bigl[(1-P)
              -(1+5\rho(1-r))(1-P_u)\bigr]_+.
\end{aligned}
\tag{CD322}
\]

When the u-axis mask excludes no mass, `P_u=1`, this forces
`5rho*Delta45>=1-P`. For a nonempty ordinary palette, P<1 and
this is a strictly positive envelope cost. It holds even though the
source-mask restriction itself adds nothing at that endpoint.
More generally, CD322 trades small excluded u-axis mass against
remaining envelope slack.

CD316 is the actual-unit bridge; CD317–322 reuse finite simplex
maximization and the existing exact budget decomposition. No new
search over palettes is required for these relations, and no new
palette exclusion is asserted. A strict whole-cover contradiction
still needs the unit residuals, actual axis allocation, source data
and colored supplier bound to satisfy one jointly evaluated inequality.
The finite-algebra exact checks are separate from the ordinary
original-family bridge and do not by themselves verify that whole chain.

### One scalar axis parameter gives a necessary relaxation

Keep the actual unit/source parameters `rho,b,r,g,d,delta_max`, the
same finite ordinary palette A and the same fixed exception set from
the d<=g branch. None is independently reselected while optimizing
ordinary axes. Put `t=P_u=product_p kappa_p`, so `P<=t<=1`, and for
nonempty ordinary support S put `P_S=product_(p in S)(1-g_p)>0`.
Because every `kappa_p>=1-g_p`,

\[
\kappa_{\rm out}(S)
  =\frac{t}{\prod_{p\in S}\kappa_p}
  \le\min(1,t/P_S).
\tag{CD323}
\]

Therefore CD307's same-support inventory is bounded above by

\[
\overline T_{\rm ax}(t)=
 \sum_{e=2}^{G}5^{1-e}
 \sum_{\varnothing\ne S\subseteq A}
  [2r_e\min(1,t/P_S)-1]_+\prod_{p\in S}g_p.
\tag{CD324}
\]

Every summand is increasing in the substituted outside-axis survival
bound. The inventory term is piecewise affine in t. When r_e<=1/2,
its layer is zero; otherwise its possible breakpoints are
`P_S/(2r_e)` and `P_S`, restricted to `[P,1]`.

The actual coordinate cap also gives
`kappa_p*eta_p=1-x_(p,u)-x_(p,v)+x_(p,u)*x_(p,v)>=1-g_p`.
Multiplying shows `P_u*P_v>=P`, hence `P_v>=P/t`.
Since M45 is increasing in P_v, define

\[
\begin{aligned}
m_{45}(t)&=t+(1-a_{45})P/t
                  -(r-a_{45})\max(t,P/t),\\
\Delta_{45}&\ge[m_{45}(t)-M_2(r)]_+,\\
c_v&\ge[P/t-\bar L]_+,\qquad
q\ge[t-\bar L-D]_+.
\end{aligned}
\tag{CD325}
\]

The last line uses CD188's complete identity
`R=L0^c intersect A_u^c intersect (B_u^0)^c`, the actual low bound
`lambda(L0)<=Lbar`, and CD191's same-root nonaxial bound
`lambda(B_u^0)<=D`. No five-free event is omitted from R.
The positive part in the Delta45 bound retains its independently
proved nonnegativity: `(t,P/t)` is a relaxation of the product
constraints and need not be attained by actual axis prefixes.

Use `d*q-min(d*q,epsilon)=[d*q-epsilon]_+`, which is increasing in
q, with `epsilon=3/350`. Substituting CD324–325 into the same CD308
consumer with CD319's envelope slack yields, at the actual t,

\[
\boxed{
\begin{aligned}
5\rho S\ge F(t):={}&5\rho[m_{45}(t)-M_2(r)]_+
                 +g[P/t-\bar L]_+\\
 &+[d[t-\bar L-D]_+-3/350]_+
                 -\overline T_{\rm ax}(t),\qquad P\le t\le1.
\end{aligned}}
\tag{CD326}
\]

Thus every actual configuration in the displayed branch satisfies
`5rho*S>=inf_(P<=t<=1) F(t)` for its same unit parameters. This maps
actual configurations into a necessary scalar constraint; it does
not construct a cover or assert an attainable scalar minimizer.
The common-axis lower bound on `c_v+q` was not consumed in CD326
and can further restrict their joint minimization at the same t.

Only the inventory term has the breakpoints listed after CD324.
The complete F also contains P/t, the switch `t=sqrt(P)`, the
roots of `m45(t)=M2(r)` and the source positive-part switch.
Within a fixed branch its form is `A*t+B/t+C`, so possible interior
stationary points must also be checked when minimizing it. No grid,
palette scan or new branch exclusion is asserted by this reduction.
It combines existing coordinate capacities, the complete source
union bound and the mandatory45 envelope; it does not supply the
remaining uniformly strict inequality for all admissible unit data.

### The common-axis relation eliminates the source mass exactly

Keep CD326's same actual unit data, ordinary palette, axis parameter
`t=P_u`, and fixed exception price `epsilon=3/350`. The complete
source also satisfies `q<=t`. Its common-axis relation is
`c_v+q>=M_2(0)-2Lbar-D`. Put

\[
\begin{aligned}
k(t)&=[t-\bar L-D]_+,&
l(t)&=[P/t-\bar L]_+,\\
C&=M_2(0)-2\bar L-D,&
q_*(t)&=\max\{k(t),\min(t,C-l(t))\}.
\end{aligned}
\tag{CD327}
\]

Here `0<=k(t)<=q<=t` and `c_v>=max(l(t),C-q)`. All quantities
refer to the same actual source and the same ordinary axis
allocation. The condition `0<=d<=g` gives the exact interval minimum

\[
\boxed{
\begin{aligned}
&\min_{k(t)\le q\le t}
 \{g\max(l(t),C-q)+[dq-\epsilon]_+\}\\
&\qquad=g\max(l(t),C-t)+[d q_*(t)-\epsilon]_+.
\end{aligned}}
\tag{CD328}
\]

To verify it, write `z=C-l(t)`. For `x<=y<=z`, the first term
decreases by `g(y-x)`, while the positive-part term increases by
at most `d(y-x)<=g(y-x)`. Thus the objective is nonincreasing
to z. For `z<=x<=y`, its first term is constant and its second
term is nondecreasing. Clamping z to `[k(t),t]` therefore gives
a minimizer, including the case `k(t)>z`. At that clamped point,
`max(l(t),C-q_*(t))=max(l(t),C-t)`, which gives the displayed value.
Neither uniqueness nor a source realization of this minimizing q
is asserted.

Replace CD326's two source terms by this one joint minimum. The
same actual configuration must satisfy

\[
\boxed{
\begin{aligned}
5\rho S\ge F_{\rm joint}(t):={}&
 5\rho[m_{45}(t)-M_2(r)]_+
 +g\max(l(t),C-t)\\
 &+[d q_*(t)-3/350]_+
 -\overline T_{\rm ax}(t),\qquad P\le t\le1.
\end{aligned}}
\tag{CD329}
\]

This is a replacement within the same debit. The common-axis
relation is not an additional amount to add to CD326, and the
exception allowance is still used once. Since `q_*(t)>=k(t)` and
`max(l(t),C-t)>=l(t)`, one has `F_joint(t)>=F(t)` pointwise.
Eliminating t gives the necessary condition
`5rho*S>=inf_(P<=t<=1)F_joint(t)` for the same fixed admissible unit
parameters.

The upper bound `c_v<=1` was omitted from this interval relaxation.
Retaining it would further require `q>=C-1`; omitting it only weakens
the bound. The exact minimum in CD328 is attained in its displayed
real interval, and need not be attained by a five-free survivor or
by any congruence family. No new arithmetic branch exclusion is
asserted here.

### Verification scope and remaining inequality

The unit-coupling, colored-mismatch, masked-capacity and joint-inventory
consumers in CD288–329 are ordinary mathematical deductions. Their
finite controls were checked by exact rational calculation and
independent enumeration. Five scoped transient Lean checks verify
nineteen statements: the finite color comparison and clipped exception
loss; masked fractional-knapsack inequalities and the explicit positive
gap; the mandatory45 finite axis algebra; the coordinate-product and
scalar substitutions into CD326; and CD328's exact interval minimum.
Their complete types and axiom closures use only `propext`,
`Classical.choice` and `Quot.sound`. These reuse checks add no retained
mathematical declaration.

The finite statements retain their displayed nonnegativity, capacity,
common-budget and interval hypotheses. They do not construct the actual
integer family, identify its complete tower/source events, or prove
the complete arithmetic bridge into those hypotheses. The full
CD288–329 chain is therefore not claimed as Lean-verified. The controls
are not whole covers, and no new arithmetic branch exclusion is
asserted. The finite upper-knapsack and separate-affinity arguments
are reused results, not new duality claims.


The pointwise finite-law check for CD263–273 retains every color,
including zero-demand colors, and verifies both alternative uses of the
same excess term. It also verifies the clipped exceptional-load loss
under the same survivor predicate. The exact five-color application
and the existing real-valued fractional-knapsack complement application
compile with the standard axioms listed below. These are finite
algebra and reuse checks, with no new retained Lean declaration.
The integer realization of the pointwise fields, the original S budget,
the actual pattern/selector identification, and the rational-to-real
interface joining these separate checks remain unverified in Lean.
A separate finite rational-law check verifies CD274–275 with the
actual intersection probability, nonnegative exception coefficients
bounded by g, and exactly the same exceptional load in its budget
consumer. It also verifies the guard-cap monotonicity, the four
rational branch bounds in CD284, and the scalar replacement by
min(g*q,3/350). These checks use the same standard axioms. They do not
derive the graph-selected weight bound from the integer cover or
identify the actual pattern law. The final threshold composition
CD278–281 and its complete arithmetic consumer remain ordinary
deductions here.


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
included. SC483 supplies none of these upper bounds by itself.
The remaining ternary-height-two cases, including other ordinary
palettes for a single exceptional5 and multiple exceptional primes,
and unrestricted odd distinct
covering remain unresolved. CD148, CD152 and CD159 exclude every
specified single exceptional prime q at least seven by full-prime-guard
arguments, with separate shared-label pools required for q=7.
