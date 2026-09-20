[Index](../../marked_head_profile.md) · [Original-label SAT transport](../321-384/343-original-prefix-sat-reductions-and-transport-obstructions.md) · [Extremal original constraints](../321-384/350-extremal-paired-branch-and-source-support.md)

# A ternary shadow can cover despite distinct downward-closed labels

There is an eleven-box cover of the full ternary cube on five coordinates
with one box per nonzero exponent vector, nonempty downward closure,
disjoint boxes at comparable distinct vectors, and a private point for
every box. Every coordinate interleaving still misses part of the cube
when restricted to its prefix-compatible boxes.

Thus those shadow constraints cannot by themselves rule out a complete
shadow cover or force a successful interleaving. The same literal boxes
also come from eleven distinct odd APs on the original prime coordinates
5,7,11,13,17, with divisor closure and private points. That actual AP
family does not cover: it has 40618 uncovered residues in period 85085.
Moreover, one probability uniform on that actual residual satisfies all
five stronger marginal bounds 1/(p-2), even though its selected ternary
product is completely covered.

These are precise obstructions to implications about compressed sources,
not an odd distinct covering system, a disproof of a common-law theorem,
or a new Lean result. The Boolean mechanism is standard unsatisfiable
2-CNF; no literature-priority claim is made.

## 1. The complete source and its eleven boxes

Let Omega={0,1,2}^5 with coordinates (a,b,c,d,e). A box fixes the
coordinates in its nonempty scope and leaves all others unrestricted.
Take the five singleton boxes a=0,...,e=0 and the following six pairs:

| Scope | Specified values |
|---|---|
| ab | a=2, b=1 |
| bc | b=2, c=1 |
| ac | a=2, c=2 |
| ad | a=1, d=1 |
| de | d=2, e=1 |
| ae | a=1, e=2 |

The singletons cover every point with a zero coordinate. On the remaining
Boolean cube, let 1 mean false and 2 mean true. Avoiding the first three
pair boxes means satisfying

    not a or b,    not b or c,    not c or not a.

If a were true, the first two clauses would force b and c true, violating
the third. Thus a must be false. Avoiding the last three boxes means
satisfying

    a or d,        not d or e,    not e or a.

If a were false, these force d and e true and then a true. No Boolean
assignment avoids all six pairs, so the eleven boxes cover Omega.

There is one box for each of eleven different nonempty scopes. Regarding
a scope as a 0/1 exponent vector, the only comparable distinct pairs are
a singleton and one of the pair boxes containing its coordinate. Their
fixed values are respectively zero and nonzero, so their boxes are
disjoint. There are twelve such comparable pairs.

The scopes already form a nonempty downward-closed family: both
singletons below every actual pair occur. Downward closure does not
require the four missing pairs or any triple. This is exactly the
distinction between all nonunit divisors of each actual modulus and
all divisors of the lcm.

## 2. Every box has a private point

Each listed point lies in its named box and none of the other ten:

| Box | Private point (a,b,c,d,e) | Total private points |
|---|---|---:|
| a=0 | (0,1,1,1,1) | 9 |
| b=0 | (2,0,1,1,1) | 3 |
| c=0 | (2,2,0,1,1) | 3 |
| d=0 | (1,1,1,0,1) | 3 |
| e=0 | (1,1,1,2,0) | 3 |
| ab | (2,1,1,1,1) | 3 |
| bc | (2,2,1,1,1) | 3 |
| ac | (2,2,2,1,1) | 3 |
| ad | (1,1,1,1,1) | 3 |
| de | (1,1,1,2,1) | 3 |
| ae | (1,1,1,2,2) | 3 |

Membership directly verifies each witness, proving irredundancy. The
counts use all 243 points and are independently checked by the program.
In particular, adding private-point existence to the shadow assumptions
does not restore the failed noncoverage implication.

An extra box added while keeping these eleven would itself be redundant,
since they already cover every point. Requiring every possible scope and
irredundancy would therefore be a different problem, not completion of
the already satisfied divisor-closure condition.

## 3. Every fixed interleaving still fails

For a permutation sigma of the five coordinates, a box becomes one
ordinary lowest-digit-first ternary prefix precisely when its scope is
an initial segment of sigma. Among the eleven boxes, these can only be
the first singleton and, if present, the pair of the first two coordinates.
Their masses are 1/3 and 1/9 and their intersection is empty. Hence

    mass(union of sigma-compatible boxes) is 1/3 or 4/9.     (TS1)

Neither value is one. This holds for every interleaving, while the whole
family covers. Of the 120 permutations, 48 give 1/3 and 72 give 4/9:
there are twelve ordered choices for the first pair whose unordered
scope is present and six permutations of each remaining triple.

Under the identification of Omega with five ternary digits of one
integer, an off-path pair fixes two digit positions that are not the
first two. If its last fixed position is j, it splits into 3^(j-2)
APs with the same numerical modulus 3^j. Therefore the shadow cover
does not become a distinct-modulus cover merely by choosing an ordering.

The total of all eleven box masses is 5/3+6/9=7/3. A bound for a
comparable chain cannot be applied to their entire incomparable family.
The exact all-source multiplicity counts at multiplicities 1,...,5
are 39,104,81,18,1.

## 4. The same literal events on five distinct odd primes

Assign coordinates a,b,c,d,e the primes 5,7,11,13,17. Give every box
the squarefree modulus which is the product of its coordinate primes,
and its unique CRT residue from the same fixed values. The eleven
moduli, in the table order, are

    5,7,11,13,17,35,77,55,65,221,85.                 (TS2)

They are distinct, odd, nonunit and divisor-closed. Comparable APs are
disjoint because the same zero/nonzero conflict remains. Every ternary
private tuple from section 2 lifts by CRT to an actual private integer.
This proves irredundancy of the original family, without asserting that
it covers all integers.

Let Q=5*7*11*13*17=85085, let C0 be this original family, and let R
be its actual residual modulo Q. The map

    Psi: {0,1,2}^5 -> Z/Q

sets the five prime coordinates to the five ternary values. It preserves
the membership of every original AP at the same source point. Thus
Psi(Omega) is entirely covered by C0. Nevertheless integer 3 lies in R:
its five prime coordinates are all 3, so it belongs to none of the
singleton or pair APs.

Full-period enumeration gives |R|=40618. For the single probability
nu uniform on R, the maximum first-prime cylinder masses are:

| Prime p | Maximum count in R | Maximum mass | Required cap |
|---|---:|---:|---:|
| 5 | 11269 | 11269/40618 | 1/3 |
| 7 | 7179 | 7179/40618 | 1/5 |
| 11 | 4231 | 4231/40618 | 1/9 |
| 13 | 3477 | 3477/40618 | 1/11 |
| 17 | 2593 | 2593/40618 | 1/15 |

Each entry is below its required cap: the corresponding cross-products
are 33807,35895,38079,38247,38895, all below 40618. These are all the
nontrivial original prefix depths, since Q is squarefree. The law is
uniform on the complete actual R, not on separately chosen projections.

Consequently, an empty selected ternary product does not imply failure
of the strong common marginal law. A dual argument which derives such
a product from a failed law is only one-way; this actual family forbids
reversing that implication. It also shows why ternary box coverage,
even with literal odd AP provenance and the stated extremal structural
properties, does not establish coverage of the original prime carrier.

## 5. Verification and the remaining arithmetic obligation

[The exact standalone program](../../frontier/cover-geometry/ternary_shadow_box_obstruction.py)
checks every ternary point, all scopes, all comparable pairs, every
private set and all 120 interleavings. Deleting each of the six pair
clauses gives Boolean survivors, providing six controls of the
unsatisfiable core. It separately constructs the CRT APs and checks all
85085 original integers, their complete event vectors, private points,
the covered selected product, the residual and the five same-law caps.
All arithmetic is integral or rational. No solver or Lean verification
is used.

The established multi-valued SAT bridge and its measure boundary are
reused from report 343. The downward-closure convention and extremal
original hypotheses are those in report 350. The existing forest
feasibility and energy results do not apply: these six pair scopes form
two triangles sharing a vertex. A search of the relevant report,
frontier, Library and congruence material found no same construction in
that scope; the standard 2-CNF mechanism is not claimed as new.

This example does not satisfy global minimality among distinct odd
whole covers: its original odd family is not a whole cover at all.
It therefore leaves unrestricted Erdős #7 and any stronger statement
using that full premise unresolved. A valid next step must retain more
of the different original prime arities, the original q-bearing family,
or a legal transformation of the entire cover. Distinct supports,
divisor closure, comparable disjointness and private points on the
ternary shadow alone cannot supply that step.
