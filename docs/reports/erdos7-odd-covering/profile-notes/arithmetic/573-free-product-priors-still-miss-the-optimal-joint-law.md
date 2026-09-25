# Arbitrary priors do not remove the product/deletion source restriction

## Exact statement and scope

Let P={3,5}. Take the actual distinct odd-modulus originals

    2 mod3, 4 mod5, 0 mod15, 1 mod45.

Let U be their complete survivor in Z_3 x Z_5. For a probability mu
supported on U define the complete, all-height query norm

    R(mu)=sum_(a,b>=0,a+b>0) max_r mu([r]_(3^a 5^b)).

Let Prod(U) contain every normalized product/deletion law

    mu=(u x w)|U / (u x w)(U),

where u is ANY ternary probability, w is ANY 5-adic probability, and
the surviving mass is positive. No fixed-u hypothesis is imposed.
Then

    min_(mu supported on U) R(mu)=203/144
       < inf_(mu in Prod(U)) R(mu) <=13/9.

The strict lower separation is an ordinary theorem proved below. The
value13/9 is a certified product-source upper bound, not a claimed
exact restricted optimum. This is a source-class separation, not an
obstruction at566/49 and not an unrestricted covering result.

[Report530](530-one-supported-law-controls-unused-and-deep-occupied-labels.md)
and [Report571](571-joint-residual-laws-retain-conditional-and-query-incidence.md)
already supply the all-height finite reduction and fixed-u variational
framework. Report571 section3.1 explicitly says its prior example is
repaired by changing u. The four-original family here
separates the class even when BOTH priors are arbitrary.

## Finite reduction preserves the source class

Resolve ternary height2 and 5-adic height1. Write a finite cell as
(t mod9,x mod5). The actual survivor cells are exactly

    t in {0,1,3,4,6,7}, x in {0,1,2,3},
    excluding (t in {0,3,6},x=0) and (t=1,x=1).

There are20 cells. This is the literal CRT image of the four originals.
Average any supported law over translations in9Z_3 x5Z_5. The mask U
is invariant, each query maximum is convex, and translations permute
query phases. Hence no query maximum, nor their nonnegative sum,
increases. The resulting law has Haar tails in every45-cell.

For a product/deletion law, these independent tail averages give

    ((average u) x (average w))|U / (u x w)(U).

The denominator is unchanged, since the finite cell masses are
unchanged. Thus the finite reduction also preserves Prod(U), even for
arbitrary non-Haar priors. Conversely every finite cell law has a Haar
lift, and every finite product/deletion source has a Haar product lift.
Both all-height infima therefore equal their corresponding finite ones.

For Haar tails put M_d=max_r mu([r]_d). Geometric summation gives exactly

    R=M3 +(5/4)M5 +(3/2)M9 +(5/4)M15 +(15/8)M45.    (1)

In particular the coefficient of M3 is1, not3/2: ternary height2 is
resolved, so only saturated exponent2 carries the geometric tail.
All higher query heights are included by(1).

## One exact dual for every supported joint law

Use the following positive weights lambda on query phases. Phases are
specified in CRT form (t mod9,x mod5); only the residues relevant to d
are used.

| d | selected query phases | weight per phase |
|---|---|---|
|3|t=0 mod3|73/144|
|3|t=1 mod3|71/144|
|5|x=1,2,3|5/12|
|9|t=1,4,7|1/2|
|15|t=0 mod3,x=1|35/72|
|15|t=0 mod3,x=2,3|25/144|
|15|t=1 mod3,x=0|5/12|
|45|t=0,3,6 and x=2,3|5/16|

For each d the phase weights sum to the corresponding coefficient in
(1). For EVERY surviving cell, the sum of weights of phases containing
that cell is203/144. Thus, integrating this pointwise constant against
any supported probability,

    R(mu) >= sum_(d,r)lambda_(d,r) mu([r]_d)=203/144. (2)

All coefficients and all20 cell identities are checked over exact
rationals in the accompanying Python certificate.

An attainer assigns1/18 to every surviving cell except the four cells
with t=4,7 and x=2,3, which receive1/36 each. Its maxima are

    (M3,M5,M9,M15,M45)=(1/2,5/18,1/6,1/6,1/18),

so its complete norm is203/144.

## The ENTIRE optimal face violates product/deletion identities

Every slack in(2) is nonnegative. Equality forces every query phase
with positive lambda to attain its corresponding maximum. For ANY
optimal law, not merely the displayed symmetric attainer, this yields:

1. The two ternary roots0,1 each have mass1/2.
2. The three cells (t=0 mod3,x=j), j=1,2,3, all attain M15.
   They partition root0, so M15=1/6.
3. The six45-cells (t=0,3,6;x=2,3) all attain M45. Summing one
   column gives3M45=M15, hence M45=1/18. The three remaining
   root0 cells at x=1 sum to1/6 and are each at most M45, so EVERY
   root0 surviving cell has mass1/18.
4. Rows t=1,4,7 each attain M9; together they have mass1/2, so
   each has mass1/6. Row1 contains only three surviving cells,
   x=0,2,3, each at most1/18. Consequently each has mass1/18.
5. The query (t=1 mod3,x=0) attains M15=1/6. Row1 contributes
   1/18, so the cells(4,0),(7,0) each have mass1/18.
6. Columns1,2,3 attain M5, while column0 has mass1/6. Therefore
   M5=5/18. Column1 has root0 mass1/6 and no row1 mass, so
   (4,1),(7,1) each have mass1/18.
7. Row4 has mass1/6 and its cells at columns0,1 already contribute
   1/9. Thus

       mu(4,2)+mu(4,3)=1/18.                       (3)

Every product/deletion law satisfies the following two polynomial
identities, since all four corners in each identity survive:

    mu(0,1)mu(4,2)=mu(0,2)mu(4,1),
    mu(0,1)mu(4,3)=mu(0,3)mu(4,1).                 (4)

But the optimal-face constraints give

    mu(0,1)=mu(0,2)=mu(0,3)=mu(4,1)=1/18.

Equations(4) would force BOTH mu(4,2)=mu(4,3)=1/18, contradicting(3).
Hence no optimal joint law can satisfy even these two product cycles.
No claim based merely on the rank of a selected matrix is used: the
objective dual forces the incompatible entries on its entire optimum
face.

## Strict infimum separation, including limits with vanishing mass

Let C be the subset of the finite probability simplex on U satisfying
just the two polynomial identities(4). It is closed and compact, and
contains every normalized product/deletion law and every limit of such
laws, even if the underlying unnormalized survival tends to zero.
The norm(1) is continuous. Thus min_C R is attained. By(2) and the
optimal-face contradiction it is strictly greater than203/144.
Therefore

    inf_Prod R >= min_C R >203/144.

This supplies a strictly positive gap without asserting a numerical
lower gap or attainment inside the possibly nonclosed product image.

## Certified product upper bound

Choose ternary root9 weights

    u_t=2/11 for t=0,1,3,6;
    u_t=3/22 for t=4,7;
    u_t=0 otherwise,

and let w be uniform on5-roots0,1,2,3, with Haar tails. Surviving mass
is9/11. After normalization all root0 cells and row1 cells have mass
1/18; the eight surviving cells in rows4,7 have mass1/24 each. Their
maxima are

    (M3,M5,M9,M15,M45)=(1/2,11/36,1/6,1/6,1/18),

and(1) gives13/9. Only this explicit upper bound is asserted for the product class.

## Evidence and limits

The [exact producer](../../frontier/cover-geometry/free_product_prior_separation.py)
and its [data](../../frontier/cover-geometry/free_product_prior_separation.json)
check the literal CRT mask, all exact dual budgets and cell identities,
the unrestricted attainer, and the product-source upper certificate.
The equality-case argument and compactness establish the strict
infimum separation; finite checks alone do not prove it. The producer
uses exact rational arithmetic and no numerical optimizer, and retains
its checks under Python optimization.

Independent unused Haar coordinates embed both classes into any finite
larger prime carrier. Conversely, averaging over those whole unused
coordinates preserves U and the product class and cannot increase any
query maximum. Thus in each class its infimum transforms as

    1 + inf R_(P union F) = (1 + inf R_P) product_(q in F) q/(q-1).

The strict separation therefore also holds in the seven-prime carrier.
This neither denies good product laws at the continuation threshold nor
settles an arbitrary-family existence claim. In particular13/9 is an
upper bound, not the claimed exact product optimum. The result limits
source-class conversion, not Erdős #7 itself. No new Lean verification
or claim of external novelty is made.
