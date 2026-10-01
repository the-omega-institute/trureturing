# One actual label dictionary sharply localizes thin singleton fibres

The [all-colour row envelope](758-one-row-mass-law-handles-all-outside-colours.md)
needs guaranteed nonempty fibres wherever its row mass is positive.
The following bounds localize the potentially empty or thin rows using
the shared old phases of the original numerical labels.

Fix arbitrary phases a_d modulo each of the eleven DISTINCT numerical
labels

    D={3,5,7,9,15,21,35,45,63,105,315}.

For x modulo315 let h(x)=#{d in D:x=a_d mod d}.  The statement below is
uniform over ALL eleven phases, and over every actual old source
X subset Z/315.  It does not identify every X with the 75-row example.

At an outside prime p, remove one pure root and then the eleven singleton
roots attached to these actual old phases. Let r_p(x) be the number of
remaining roots. The labels that hit x may remove coinciding roots, or the
already absent pure root; hence

    r_p(x)>=max(p-1-h(x),0).                                      (H1)

The right side is a lower bound on an actual count, not a claim that all
lower counts are jointly realizable by one root assignment. In particular
at11 an eleven-injective palette on ten live roots does not exist.

## 1. Four phase-uniform heavy-row bounds

For every phase dictionary,

    #{h>=10}<=1,  #{h>=9}<=2,  #{h>=8}<=3,  #{h>=7}<=4.          (H2)

Consequently at11,

    #{r11<=j}<=j+1,                       j=0,1,2,3.              (H3)

This includes possible empty fibres. All four bounds are sharp, even when
restricted to the same actual 75-row core listed below.

### Common-label geometry

For two distinct rows x,x', any label satisfied by both divides x-x'.
Thus if h(x),h(x')>=t, at least 2t-11 divisors from D divide x-x'.
The possible gcd(x-x',315) are therefore:

| t | Possible nontrivial gcd for distinct rows |
|---|---|
|10|none|
|9|105|
|8|45,63,105|
|7|15,21,35,45,63,105|

This follows from #{d in D:d divides g}=tau(g)-1 for g dividing315.
The finite checker evaluates all314 nonzero differences.

The t=10 row proves the first bound immediately. For t=9, all rows lie in
one mod105 fibre. The seven labels dividing105 can be common, while each
of {9,45,63,315} can hit at most one member of that fibre. Each high row
needs at least two of these four labels, so there are at most two.

For t=8, all rows first have a common residue mod3. Within that residue,
write the remaining coordinates as CRT(3,5,7): the first coordinate is the
remaining choice of residue mod9. The gcd table says each pair differs in
at most one coordinate. Such a set lies on a single coordinate line: fix
two different points, whose difference is in coordinate j; a third point
varying a different coordinate would differ in two coordinates from one
of those two points.

Thus all high rows share a mod45, mod63, or mod105 residue. A mod105 fibre
contains three rows. On a mod45 or mod63 fibre, only five labels divide
the common modulus; each of the remaining six labels can hit at most one
row of that fibre. Every high row needs at least three remaining labels,
so these fibres support at most two high rows. This proves the t=8 bound.

### The t=7 bound

Project the rows modulo105 and use CRT(3,5,7). The t=7 gcd table again says
two distinct projected points differ in at most one coordinate. Hence the
high rows all lie in one mod15, mod21, or mod35 fibre; each mod105 point
can have up to three lifts modulo315. A singleton projected set also lies
in each of these kinds of fibres, so no case is omitted.

On a mod15 fibre, three labels {3,5,15} contribute at most three common
hits. The remaining geometry is a 3 by7 table:

- {9,45} supply two whole-line increments along one direction;
- {7,21,35,105} supply four whole-line increments in the other direction;
- {63,315} supply two single-cell increments.

On a mod21 fibre the same description holds on a 3 by5 table, with the
two line labels {9,63}, four opposite line labels {5,15,35,105}, and two
point labels {45,315}. A phase incompatible with the common fibre supplies
no increment. Padding an absent increment gives an upper bound, so it is
enough to use the full budgets2,4,2.

Every high row requires at least four extra hits. Up to permutation the
two-line budget is (2,0,0) or (1,1,0), and the four-line budget has only
the partitions in the following table. Giving the two point increments
to the cells with the smallest positive deficits yields the displayed
maximum number of cells that can reach four extra hits:

| Four-line partition | Two-line (2,0,0) | Two-line (1,1,0) |
|---|---:|---:|
|4|4|3|
|3+1|3|3|
|2+2|3|2|
|2+1+1|3|2|
|1+1+1+1|2|1|

This proves at most four on either grid. As a separate exact verification,
the consumer checks every allocation:420 allocations for3 by5 and1260
for3 by7, with the same maximum4. Its treatment of point placement is
exact: reaching a cell requires exactly its threshold deficit, and choosing
the cheapest deficits maximizes their count under the point budget.

On a mod35 fibre, {5,7,35} contribute at most three common hits. There are
three groups of three rows distinguished modulo3. The four labels
{3,15,21,105} each increment one whole group, and {9,45,63,315} each
increment one point. The group-budget partitions4,3+1,2+2,2+1+1 give,
after the four point increments, maxima4,3,2,2. The consumer checks all15
labelled group allocations. This completes the t=7 proof and thus(H2).

### Actual sharp witnesses

Use the single actual core

    (3,0),(5,0),(7,0),(9,4),(15,11),(21,8),
    (35,9),(45,1),(63,1),(105,59),(315,179).

Its survivor set has75 old rows. For each j=0,1,2,3, the consumer outputs
one literal family containing the pure class(11,0) and all eleven distinct
classes modulo11*d. Its thin rows are exactly:

| j | Actual rows with r11<=j |
|---|---|
|0|2|
|1|2,107|
|2|2,107,212|
|3|2,17,107,212|

Each literal CRT phase is range-checked. For all315 old rows the checker
reconstructs actual root sets from those numerical classes and compares
their counts to the color calculation. The examples certify sharpness;
the universal assertion is supplied by the preceding proof.

## 2. What these bounds give a row-law construction

For fixed old singleton phases on all five axes, set

    r_j^*(x)=max(p_j-1-h_j(x),0).

At the smallest primes(11,13,17,19,23), only the11 axis can have a zero
lower count, and(H2) says its excluded set has at most one row. A row law
u used with this lower-count envelope must assign zero mass there even if
some actual root collision pattern leaves that row nonempty. Such a
choice is lawful because the final source is constructed on actual
surviving fibres using the same old marginal u.

At11 the rows with lower counts at most1,2,3 are respectively at most
2,3,4. The same h-threshold estimates apply separately to each other axis,
with lower-count thresholds shifted by p_j-11. These are joint geometric
restrictions on each axis's phase dictionary; they do not allow choosing
the most adverse row set separately for every query.

For any prescribed old probability v, discarding the zero lower-count
row loses at most max_x v_x. Discarding all rows with r11^*<=j, j<=3,
loses at most the sum of its j+1 largest masses. These are bounds on loss
of the same prescribed marginal. They do not establish that the remaining
source passes the query-cost criterion: its surviving mass, each query,
and its maximum density all still need to be charged jointly.

## Exact verification and scope

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_thin_fibre_geometry.py)
checks the complete nonzero-difference geometry, every small line-budget
allocation, and the four sharp numerical CRT witnesses. Its
[retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_thin_fibre_geometry.json)
contains all literal originals and must equal a fresh full recomputation.

An independent implementation places the point increments explicitly,
instead of using the deficit-greedy calculation:50400 placements on the
3 by5 grids,291060 on the3 by7 grids, and7425 on the grouped geometry.
The maximum remains4 in all three cases. It also computes the pair table
from divisors directly and reconstructs13860 numerical CRT root queries;
all four sharp witnesses agree.

The universal phase bounds follow from the common-label and allocation
proof above. Exact finite computations verify the stated supporting
lemmas and sharp examples; neither is new Lean verification. These
bounds control low fibre cardinalities, but do not prove the row-envelope
budget positive for every old-phase dictionary. The complete query
incidence relations and the same-source weights remain necessary inputs
to any proposed positive certificate. Unrestricted Erdős #7 is unresolved.
