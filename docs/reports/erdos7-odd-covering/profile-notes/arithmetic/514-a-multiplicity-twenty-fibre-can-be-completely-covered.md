# A multiplicity-twenty fibre can be completely covered

A finite family of later congruence classes with moduli23^j29^k, j,k>=0
and j+k>0, can cover its whole fibre with at most20 classes for each
numerical later modulus. An explicit family uses129 classes, heights at
most two on both axes, and period444889=23^2*29^2.

It lifts to129 pairwise distinct original odd numerical moduli using just
20 old cofactor labels. Those original classes cover the fibre of one old
point, while integer1 avoids the whole lifted family. Thus this is not an
Erdős#7 counterexample.

The construction refutes extending the single-fibre safe condition Q<=19
to Q<=20 from only a bound on active old-label count. It does not refute
multi-point constraints, actual-source occupation conditions, or stronger
boundary representations. All claims here are ordinary finite mathematics
and exact checks, not Lean verification or a claim of literature novelty.

## The seven layers use fixed residues

Use coordinates x mod529 and y mod841. In the table a pair(a,b) denotes
one CRT residue modulo the indicated product. All classes are chosen once;
the stage order merely explains their union.

| Layer | Modulus | Fixed residues or CRT pairs | Count |
| --- | ---: | --- | ---: |
| 1 | 23 | 0,...,19 | 20 |
| 2 | 29 | 0,...,19 | 20 |
| 3 | 667 | {20,21} times {20,...,28}, and(22,20),(22,21) | 20 |
| 4 | 529 | 22+23a, 0<=a<20 | 20 |
| 5 | 15341 | {482,505} times {22,...,28}, and(528,b),22<=b<=27 | 20 |
| 6 | 841 | 28+29b, 0<=b<20 | 20 |
| 7 | 444889 | (528,28+29b),20<=b<=28 | 9 |

After layers1 and2, the only possible first digits are x=20,21,22 mod23
and y=20,...,28 mod29. Layer3 covers the first two rows and two cells of
the last row. What remains has x=22 mod23 and y=22,...,28 mod29.

Layer4 leaves just three second23 digits a=20,21,22, whose x residues
are482,505,528. Layer5 covers twenty of the resulting21 cells, leaving
only x=528 mod529 and y=28 mod29. Layer6 then leaves the nine second29
digits b=20,...,28. Layer7 covers all nine.

This proves coverage by the listed static finite family. The exact numbers
of remaining residues in the full period after the seven layers are

    58029, 18009, 4669, 609, 29, 9, 0.

The modulus multiplicities are20 for23,29,529,667,841,15341 and9 for444889.

## Lift without identifying distinct original moduli

Order the classes in each row as in the table. Give the class with index i,
starting at0, the old label d_i=3^i. For a projected class a mod n, let R be
the unique CRT residue with

    R=0 mod d_i, R=a mod n,

and use the full original class R mod(d_i*n).

All129 full moduli are odd and greater than one. Unique prime factorization
separates rows with different23/29 exponent pairs; the different powers of3
separate the labels within a row. Hence all full numerical moduli are
pairwise distinct. The only old labels used are1,3,...,3^19.

At old point0 mod3^19 every selected old condition is satisfied. Restricting
the original classes to this old point gives exactly the projected family
above. Thus all new-coordinate fibres above this old residue are covered.

Conversely, integer1 avoids every full class. If i>=1, it already fails
R=0 mod3^i. For i=0 the seven projected residues are the first listed class
in their row, and none contains1. The consumer checks this against all129
literal original CRT residues. The construction therefore exhibits a
covered old fibre inside an original family with an explicitly uncovered
integer.

No old cofactor labels have been merged into one original numerical modulus.
The repeated moduli occur only after taking the same-old-point projection.
A distinct-modulus theorem cannot be applied to that projection without
accounting for its multiplicities.

## The exact boundary of the single-fibre count criterion

If each later numerical modulus has at most Q classes, the two pure-axis
unions have masses at most Q/22 and Q/28, and the full mixed union has
mass at most Q/616. For Q<=19, the product structure before mixed deletion
therefore gives the established lower bound

    s >= (1-Q/22)(1-Q/28)-Q/616
      >= (1-19/22)(1-19/28)-19/616
      =1/77>0.

The first inequality retains one actual pure family and its product
survivor set; the mixed union bound includes every positive exponent pair.
The infinite geometric sums upper-bound each finite inventory. Both pure
factors are nonnegative in this range, and the expression decreases as Q
increases through0,...,19.

The finite construction at Q=20 shows that20 is the first integer
multiplicity allowing complete coverage in this particular projected
23/29 model. It does not imply that every Q=20 boundary is coverable, or
that the129-class construction is minimal in number of classes or heights.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_prime_multiplicity_twenty.py

The standard-library consumer constructs every projected and lifted
original CRT residue. It scans all444889 integer residues, independently
checks all529*841 coordinate pairs, verifies every intermediate count,
and checks distinctness and the original avoiding integer. It compares
the deterministic result with its adjacent JSON by default. The seven-layer
argument above supplies the explicit mathematical cover.
