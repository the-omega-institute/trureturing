[Index](../../marked_head_profile.md) · [Complete AP repair interfaces](365-coloring-literature-and-reconfiguration-interface.md) · [Actual shallow sources](366-shallow-tail-truncation-on-the-actual-source.md) · [Minimum-height ties](367-prime-parent-eligibility-and-height-ties.md)

# Joint source selection can require strictly greater height

An actual whole-cover control strengthens 367's minimum-height obstruction.
There are 655 original prime-private sources. Their independent minimum
selection heights sum to 963, but every family attaining 963 repeats a
residual original-label slot. Unit-slot-compatible maximum selections do
exist; their exact minimum height is 964.

Consequently, a secondary objective restricted to the independent
minimum-height families cannot always remove collisions. This obstruction
already occurs between two sources, so a cycle is not required. It is a
counterexample to the unrestricted equal-height repair assertion in this
whole-cover model, not to a theorem with additional extremal odd-cover
hypotheses. The control contains even moduli and does not settle Erdos #7.

## 1. The original cover and exact selection problem

Use the twenty original APs

    (0 mod 2), (0 mod 3), (0 mod 5), (5 mod 6), (0 mod 7),
    (4 mod 9), (1 mod 10), (3 mod 14), (4 mod 15), (4 mod 21),
    (8 mod 25), (7 mod 30), (33 mod 35), (43 mod 45),
    (23 mod 50), (28 mod 75), (13 mod 105), (93 mod 175),
    (163 mod 225), (43 mod 525).

Their complete period is Q=3150. The modulus labels are distinct and
closed under divisors greater than one. Every point is covered, every
class has a private witness, and comparable original classes are
disjoint. All source and target masses use the original uniform law on
Z/QZ. The computation retains the literal residues and all prime-power
heights, including the full tails of each private source.

At each original source s=(q,y), y in Priv_q, let M_s be the complete
menu of maximum matchings in 366's actual truncated nonpure graph,
retaining its forced height-one edges. For M in M_s define

    h_s(M) = sum_(d in M) v_q(d),
    Phi((M_s)_s) = sum_s h_s(M_s).

An edge labeled by the original d lifts to the original point obtained
by changing only y's first q-digit to a_d mod q. A residual slot is
(z,d), where z avoids all prime classes and is covered by at least two
original labels. A family is slot-compatible if each such slot is used
at most once across all its sources. This additional constraint concerns
actual selected original labels; an edge absent from every maximum menu
is not an available selection.

The assertion being tested is:

> If slot-compatible families exist, some slot-compatible family attains
> the sum of the independent local minimum heights.

The control below refutes this assertion without changing any local
rank, forced-edge obligation or cutoff.

## 2. Two sources force an extra unit of height

At the original point z=1063, the active family is

    E(z) = {105,225}.

Resetting its first 3-digit or first 5-digit to the corresponding prime
class gives the private sources

    T_3(z)=1413 in Priv_3,
    T_5(z)=685 in Priv_5.

The complete local data are:

| Source | Full height | Cutoff | Forced labels | All maximum menus | Minimum height |
| --- | --- | --- | --- | --- | --- |
| (3,1413) | 2 | 2 | {6} | {105,6}, {225,6} | 2 |
| (5,685) | 2 | 1 | {10,15,30} | {10,30,105,15} | 4 |

At the first source, the two nonprime-root rows are {105,225} and {6}.
The colors of 105 and 225 are respectively 35 and 25. Their 3-heights
are one and two; 6 has height one. Thus {105,6} is the unique local
height minimum, while {225,6} has height three.

At the second source, the four rows are {10}, {30}, {105}, {15}.
Their 5-free colors are 2,6,21,3 and every edge has height one. There
is only one maximum menu, with total height four.

Both unique local minima select 105 and lift it to z=1063. Hence they
both occupy (1063,105). No choices at any other source can remove this
double use. Every global family of independent minima therefore fails
the unit-slot requirement.

For compatibility, the first source must select 225 instead. This
preserves both matched roots, distinct colors, maximum rank, the forced
6-edge and its original cutoff two. It increases the local height by
one. The second source cannot choose 225: its 5-height is two, above
that source's cutoff one. All of these are original AP incidences.

## 3. The complete minima are 963 and 964

The complete local menus give

    sum_s min_(M in M_s) h_s(M) = 963.

A family attaining this sum must attain each local minimum separately.
Section 2 excludes compatibility for every such family. Since heights
are integers, every compatible family has total height at least 964.

For attainment, form the simple source-interaction graph: two source
vertices are joined when some choices in their complete maximum menus
share a residual slot. Every common slot for a pair is enforced in its
one joint relation. There are six shared slots and ten involved sources,
forming the following five disjoint two-source components:

| Source pair | Independent minimum | Compatible minimum |
| --- | --- | --- |
| (3,153), (5,2575) | 6 | 6 |
| (3,1203), (5,475) | 6 | 6 |
| (3,1413), (5,685) | 6 | 7 |
| (3,2463), (5,1735) | 6 | 6 |
| (3,3093), (5,2365) | 6 | 6 |

All remaining sources can use a local height minimum. Enumerating the
complete paired menus produces the displayed compatible minima; taking
these choices together gives a complete family with every residual
slot occupied at most once and total height

    963 - 5*6 + (6+6+7+6+6) = 964.

Weighting every source point by its original Haar mass 1/3150 gives
the same strict gap, namely 1/3150; no source is renormalized separately.

This checks the original complete source family, not an optimization
on separately resampled marginals. The construction does not enumerate
the Cartesian product of all 655 menus: components have no shared
slots, and the final assembled family is independently checked at
every source and every residual slot.

## 4. The precise RRO gluing boundary

The existing [running-intersection result](../../../../../D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean)
extends every specified local row to a global raw join when the finite
tree has nonempty local relations, running intersection and equality of
complete separator projections. A source variable here
is a whole local matching; a two-source relation requires that their
choices avoid every common slot. This retains the original numerical
labels, not only colors or individual incidence bits.

On the minimum-height domains, the relation between (3,1413) and (5,685)
is empty. Tree structure cannot repair that failure. If both full
maximum menus are allowed at the first source, the relation is nonempty,
but it forces the height-three choice. Removing unsupported local
choices then gives compatible separator projections, with the increased
joint cost explicitly retained.

Thus the obstruction is already in local common feasibility at the
proposed price. It does not require a global topological cycle. RRO's
existence result does not turn incompatible cheapest options into a
common cheapest option.

No Lean application or new Lean declaration is introduced here. The
existing gluing theorem identifies the relevant hypotheses; the direct
finite construction in section 3 verifies this control.

## 5. Verification and remaining research obligation

The [standalone exact checker](../../frontier/comparison-bounds/joint_minimum_height_cost.py)
verifies literal full-period coverage, private witnesses, divisor closure,
comparable disjointness, full cofactor/tail sources, Hall maximum ranks,
forced menus, local minimum heights and all shared-slot components. It
checks the assembled compatible family and its exact cost. It requires
only the Python standard library, retains checks under `-O`, and uses
no repository imports, solver or external data.

The checker passes 9,626 checks over 3,150 period points and all 655
sources, including 2,298 Hall subsets, 888 maximum menus and 884 local
height minima. An isolated copy in a path containing spaces gives
byte-identical JSON under `python3 -I -S -O -B`. Independent source
enumeration by root choices gives the same two critical menus and
the same complete costs 963 and 964.

The general odd-cover problem still requires either additional arithmetic
structure excluding this obstruction in the relevant extremal setting,
or a legal whole-AP transformation that can pay for height increases
while strictly improving a justified global objective. A compatible
source selection alone does not certify such a replacement, its complete
coverage obligations or distinct output moduli. A secondary objective
confined to the independently cheapest face is insufficient in the
whole-cover class tested here.
