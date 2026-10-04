[Index](../../../marked_head_profile.md) · [Grouped shallow slots](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment)

# Cofactor-dependent codes with protected owner subtrees

Keep the original EB1 family, $H_3=2$,
$q\in\{101,103,107,109,113\}$, $r=(125-q)/2$, and
$Q=9q^GW$ with $(W,3q)=1$ from [Report 388, Section 74](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment). A first-digit
code can depend on a retained cofactor coordinate without
splitting its original inverses if every moving digit subtree
has only owners that fix that coordinate. The construction
below gives a phase-sensitive obstruction and a moment under
one simultaneous code law. It does not supply the required
inventory of movable digits or a contradictory upper bound.

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

The outstanding requirements are a bound forcing enough
movable digits in the same actual family, control of its
actual phase and color distribution, and an upper bound
contradicting CD8 after accounting for all surviving
monochromatic and higher-support groups. SC483 supplies none
of these by itself. CD1--CD10 are ordinary mathematical
deductions without a claim of Lean verification. The
height-two branch and unrestricted odd distinct covering
remain unresolved.
