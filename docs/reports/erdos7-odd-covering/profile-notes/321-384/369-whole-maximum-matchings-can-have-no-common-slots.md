[Index](../../marked_head_profile.md) · [Actual sources](366-shallow-tail-truncation-on-the-actual-source.md) · [Joint height cost](368-joint-selection-can-require-extra-height.md)

# Whole maximum matchings can have no common slot assignment

There is an actual irredundant, divisor-closed, comparable-disjoint cover
of period 3150 for which no family of local maximum matchings respects
unit capacity at every original residual slot. This holds for the full
source graphs, with every original height retained, even without forced
edge obligations. It also holds for the shallow graphs of 366.

Three actual sources must each select one of just two slots at the same
original point. Thus allowing greater height does not always repair the
obstruction found in 368. This is a whole even-cover counterexample to a
general maximum-selection mechanism. It does not refute an assertion
restricted to extremal odd covers, and does not settle Erdos #7.

## 1. Complete cover and selection problem

Use the following 24 original classes:

    (0 mod 2), (0 mod 3), (0 mod 5), (5 mod 6), (0 mod 7),
    (7 mod 9), (9 mod 10), (13 mod 14), (7 mod 15), (4 mod 21),
    (16 mod 25), (8 mod 35), (19 mod 42), (28 mod 45),
    (11 mod 50), (58 mod 63), (31 mod 70), (31 mod 75),
    (73 mod 105), (51 mod 175), (121 mod 225), (1 mod 315),
    (121 mod 350), (1 mod 525).

The least common multiple is Q=3150. Every period point is covered,
every class has a private witness, all nonunit divisors of each modulus
are present, and any two comparable original classes are disjoint.
There are 595 prime-private sources: 397 for prime 2, 165 for 3,
25 for 5, and 8 for 7.

For a source (q,y), where y is covered only by the prime class q,
change only the first q-adic digit of y to a nonprime root r. Keep its
complete higher q-digits and its cofactor modulo Q/q^H unchanged.
Call the resulting original period point z_r. Each original mixed class
d=q^e m covering z_r gives an edge from r to its q-free color m.
A matching uses distinct roots and distinct colors, retaining its
literal original label d. The full graph includes every such height e.

For comparison, the shallow graph restricts e to the cutoff of 366:
the (q-1)-st largest compatible column height at the source cofactor.
The checker reconstructs both graphs from the literal cover, including
every private tail; it does not supply independently chosen rows.

A residual slot is (z,d), with z avoiding all original prime classes
and covered by at least two original classes, one of them d. Only
selected edges landing at residual points use residual slots; other
targets are outside this capacity constraint. The proposed joint rule
requires at most one use of each residual slot across all sources,
while every source retains its maximum matching rank.

## 2. Three sources require two slots

At the original point z=1 the complete active family is

    E(1) = {315,525}.

Resetting its first digit to the prime residue zero gives three actual
private sources:

    T_3(1)=351,     T_5(1)=3025,     T_7(1)=1351.

Their full rows, ordered by r=1,...,q-1, are:

| Source | Full height | All nonprime-root rows | Maximum rank |
| --- | ---: | --- | ---: |
| (3,351) | 2 | {315,525}; {6} | 2 |
| (5,3025) | 2 | {315,525}; {15}; {35,45}; {10} | 4 |
| (7,1351) | 1 | {315,525}; {175}; {70}; {21}; {42}; {14} | 6 |

The ranks are q-1: each source admits a matching saturating every root,
and no matching can exceed the number of roots. Consequently every
maximum matching must use root 1. At that root its original label is
315 or 525, and its original target is exactly z=1.

Thus all three sources must use a slot in

    {(1,315),(1,525)}.

Unit capacity permits at most two uses. Three are required. No joint
family exists, regardless of costs, tie-breaking or choices at the
other 592 sources. The full menus have respectively 2, 4 and 2 members;
all 16 triples fail the unit-slot condition.

This proof does not require forced edges. The globally singleton mixed
root obligations are {6}, {10,15}, and {14,21,42}; the displayed
maximum menus already contain them. A row singleton at one particular
source is not thereby a globally forced root.

All three shallow cutoffs are one. Truncation removes 315 from the
first source's root-1 row and 525 from the second source's root-1 row.
The third source keeps both. Every rank remains q-1, giving 1, 2 and 2
maximum menus, respectively. All four triples therefore fail as well.

Randomization cannot make these local maxima feasible even if capacity
is required only in expectation: for any joint distribution of them,
the sum of the expected loads on the two slots is exactly three,
whereas two expected unit bounds would make that sum at most two.
Under the original Haar law each source point has mass 1/Q; the same
comparison is 3/Q against 2/Q. No source is renormalized separately.

## 3. What the RRO gluing theorem requires

The existing [running-intersection theorem](../../../../../D5/S3/ConceptDynamics/Gluing/RunningIntersectionRecords.lean)
requires a tree of nonempty local relations, running intersection of
their variables, and equality of complete separator projection images.
A variable here must be the whole matching at one source. A relation
between two variables enforces every shared actual slot.

In the full critical graphs, the sources' target sets intersect only at
z=1. Hence each pair relation simply requires different choices of
315 versus 525 there. Each pair relation is nonempty and projects
onto both entire matching menus: its compatible-pair counts are 4,
2 and 4. Nevertheless their three-way join is empty. The three
pair bags form a cycle; no tree on those bags has running intersection
for every source variable. Keeping a spanning tree would drop an
actual capacity constraint. This is an actual AP realization of the
two-color triangle obstruction, not an application of the tree theorem.

In the shallow graphs, the first two sources always use different
slots, so their mutual relation imposes no restriction. The remaining
two constraints form a path through the third source. Compatibility
with (3,351) requires the third source to choose 315; compatibility
with (5,3025) requires it to choose 525. Each relation is nonempty,
but their projections on the shared third-source variable are disjoint.
There is no separator consistency, despite the path shape.

Thus two distinct missing hypotheses are visible in the same complete
cover: the full pair relations lack running intersection, while the
shallow path lacks consistent separator projections. The existing
theorem supplies neither absent condition. No new Lean wrapper or
formalization is introduced here.

## 4. Verification and remaining obligation

The [standalone checker](../../frontier/source-budgets/whole_maximum_slot_obstruction.py)
uses only Python's standard library. It verifies the literal whole
cover, private witnesses, divisor closure, comparable disjointness,
complete CRT source coordinates, every full and shallow source graph,
maximum ranks by both menu enumeration and Hall cuts, and the actual
critical slot and pair relations. Checks remain active under `-O`.

The checker passes 7,457 checks, including 4,732 Hall subsets and 875
literal root lifts. A detached copy run from outside the repository,
in a path containing spaces with `python3 -I -S -O -B`, produces
byte-identical output to the normal run.

The complete source ranks sum to 863 in each graph variant. There are
881 full maximum menus in total, of which 877 retain the forced edges;
the corresponding shallow totals are 853 and 849. These are sums of
local menu counts, not counts of globally compatible choices. No such
global maximum family exists.

This finite exact certificate is not a Lean proof. Its role is to
exclude a proposed general repair mechanism while retaining the
original arithmetic sources. An odd-cover argument must supply extra
arithmetic structure excluding this obstruction, or justify a rule
that relaxes local maximality or pays for repeated slots. Even a
feasible selection would still need a legal whole-AP transformation
preserving complete coverage and distinct output moduli.
