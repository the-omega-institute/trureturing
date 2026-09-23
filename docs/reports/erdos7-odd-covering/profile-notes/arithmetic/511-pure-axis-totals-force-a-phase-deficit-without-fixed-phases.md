# Pure-axis totals force a phase deficit without fixing the phases

Keep the old points, common two-centre residues, weights(17,16,13) and
eighteen complete first-mixed moduli of
[report510](510-sharp-phase-block-deficit-at-a-fixed-pure-boundary.md).
The pure23 and pure29 phases and selectors may now be arbitrary. Let
t2=22*alpha23 and u2=28*alpha29, where the alphas are the actual pure-axis
deletion fractions at old point2 on the full uniform new-coordinate fibres.
If

    t2>=3729/184,       u2>=1477/116,                     (P1)

then every choice of one allowed old selector and one shared phase pair per
mixed label deletes weighted mass at most

    373/667                                             (P2)

from the joint pure-survivor sets. The fixed independent geometric capacity
of this block is382/667, so the saving is at least9/667. The report510
construction satisfies P1 and attains P2. Thus the upper bound is sharp
over this enlarged class of pure boundaries; it need not be attained at
each individual boundary in that class.

P1 is weaker than the height-two losses in report510, and no closeness to
its particular pure phases is required. This gives a conditional inequality
that can be applied to actual pure-axis totals. It does not supply the
missing source mass or a new global support exclusion. The result is an
ordinary mathematical deduction with exact rational checks, not a new Lean
verification or an unrestricted Erdős#7 conclusion.

## A sharp upper bound for the largest phase cells

For an integer p>=1 and real0<=A<=p, let pack_p(A) be the vector with
floor(A) entries equal to1, one entry A-floor(A) if this is nonzero, and
the remaining entries zero. For a nonnegative p by q table, let Top_n be
the sum of its largest n entries, including zeros when needed; take
0<=n<=pq.

For a in[0,1]^p, b in[0,1]^q with sum a<=A and sum b<=B,

    Top_n(a tensor b)
      <=Top_n(pack_p(A) tensor pack_q(B)).               (P3)

The right side is the exact maximum over these continuous constraints.

Proof. Top_n(a tensor b) is the maximum, over n chosen table cells E, of
sum_((r,s) in E) a_r*b_s. It is coordinatewise nondecreasing and convex
in a when b is fixed, and convex in b when a is fixed. Enlarge coordinates
to reach the two sum bounds; the upper bound cannot decrease.

The polytope {a in[0,1]^p:sum a=A} has at most one nonintegral coordinate
at a vertex: two such coordinates can be perturbed in opposite directions,
expressing the point as a nontrivial midpoint. Its vertices are therefore
exactly the permutations of pack_p(A). A convex function on this compact
polytope has a maximizing vertex. First choose such a vertex for a with b
fixed; then choose a maximizing vertex for b with that a fixed. Neither
step decreases the value. Permuting either vector leaves the multiset of
products unchanged, proving P3. The packed pair is itself in the
continuous domain, proving equality of the maximum. This argument also
covers zero or integral budgets and n=0.

P3 is a relaxation. It does not assert that a packed vector with arbitrary
real entries can be produced by an actual finite odd-modulus family.

## The actual arithmetic map into P3

At one fixed old point, pure23 and pure29 classes depend on separate new
coordinates. Their joint survivor set is R23 times R29 under the full
uniform product fibre. For each first23 digit r and first29 digit s, put

    a_r=23*mu23(R23 intersect {x=r mod23}),
    b_s=29*mu29(R29 intersect {y=s mod29}).               (P4)

These numbers lie in[0,1]. The survivor mass inside first cell(r,s) is
a_r*b_s/667. Summing P4 gives

    sum a=23*(1-t2/22),
    sum b=29*(1-u2/28).                                 (P5)

Thus P1 is precisely the pair of sufficient upper bounds

    sum a<=29/16=1+13/16,
    sum b<=253/16=15+13/16.                             (P6)

No individual first cell is claimed to have density at most13/16: many
may exceed it. P3 bounds their combined largest-cell response by that of
the packed table. That table has15 entries equal to1 and every other
entry at most13/16. For0<=n<=18,

    Top_n(a tensor b)
      <=n-(3/16)*(n-15)_+.                             (P7)

The bound in P7 is attained by the packed table for every n in this range.
Repeated phase choices occupy fewer than n different cells and cannot
increase the union. P4–P7 therefore apply to every actual selection of n
first-mixed labels active at this old point.

The product in P4 is justified by pure-axis separation and the uniform
product base. Arbitrary conditioning can create a correlated base and does
not preserve this formula. Additional deletions may shrink the surviving
sets after this upper bound is obtained; they do not authorize replacing
the base law with a different one.

## Combine phase occupancy with the original selectors

The18 labels are exactly those in report510 whose maximizing old selector
necessarily activates point2. Their independent weighted scores sum to382;
each nonmaximizing selector loses at least3. These are properties of the
original old masks, and remain true after the pure phases change.

If c selectors are nonmaximizing, at least18-c labels activate point2.
By P7 their weighted phase-occupancy loss, compared with their chosen
full-cell capacities, is at least

    16*(3/16)*(3-c)_+/667.

Add the independent selector loss3c/667. The loss relative to the fixed
382/667 ceiling is at least

    [3c+3*(3-c)_+]/667 >=9/667,                         (P8)

which proves P2. The loss from phase occupancy is computed after fixing
the same actual selectors; it is not a second charge for selector regret.
No independent phase choices are granted to the different old points.
All other points' phase losses were merely discarded on the lower side.

This proof allows arbitrary finite pure cutoffs and arbitrary pure old
selectors and phases satisfying P1. It does not require every possible
pure label to be present. The mixed block still consists of the same
eighteen numerical labels667*d, with the two specified old residues and
one shared phase pair per label. Missing mixed labels can be virtually
filled only when retaining the complete block's comparison capacity.

For report510's actual pure family at J=K=2, the totals are

    t2=11088/529>3729/184,
    u2=10920/841>1477/116.                              (P9)

Its unchanged222-class CRT witness attains373/667, so the upper bound
over the class satisfying P1 is sharp. At a different pure boundary, some
individual label capacities can fall below their geometric maxima.
Accordingly P8 is not a uniform9/667 lower bound on the difference between
newly optimized individual capacities and their joint optimum.

## A computable boundary inequality and its remaining use

For general measured totals, set A=23*(1-t2/22), B=29*(1-u2/28), and write
T_n(A,B) for the packed-table expression in P3. The same proof gives

    block deletion <=[382-D(A,B)]/667,
    D(A,B)=min_(c=0,...,18)
      [3c+16*(18-c-T_(18-c)(A,B))].                     (P10)

The function n-T_n is nondecreasing because each table entry is at most1;
this justifies replacing the actual number of point2 activations by its
lower bound18-c. P10 is an upper bound for every actual family in the
declared interface. It is not an exact optimization of the full shared
phase problem for each A,B.

This is additional information derivable from two axis totals and the
known product-cell structure. It does not make those totals a dynamically
sufficient state: report504's equal-total families still have different
responses to a specified continuation. An upper envelope can depend on
coarser data without determining the exact response.

As in report510, the deficit can be subtracted once from a complete mixed
inventory containing this block. To obtain a global improvement, one must
still control which actual source histories satisfy P1, or integrate a
useful P10 under the same incoming law with complementary histories
accounted for. The source cannot be replaced by the three-point weights,
and the fixed two-centre old interface has not become arbitrary old
residue data. No new global support constant follows from P1–P10 alone.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/packed_phase_cell_bound.py

The standard-library program implements the packed-table bound and P10,
checks the exact thresholds and all19 selector-count branches, and checks
the report510 sharp witness against the enlarged conditions. Small exact
grid controls exercise the general bound, including zero and integral
budgets; P3's quantified proof is the convexity argument above.
