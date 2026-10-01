# A marked boundary computes the actual deletion budget on one source

Fix a finite old core X and distinct outside primes p. Suppose every actual
outside-bearing original uses only one outside prime, at exponent one.
Originals may use arbitrary old cofactors. For each surviving old point x,
let A_p(x) be the set of p-roots avoiding all such originals and the pure
p exclusion. These sets come from the globally fixed original phases.
Put r_p(x)=|A_p(x)|. The actual survivor count is exactly

    Z=sum_x product_p r_p(x).

This formula requires the stated absence of originals with two outside
primes. It follows from the Cartesian product of the remaining fibres
at each fixed x; it asserts no independence of coordinates after averaging x.

For an old divisor d and outside subset J, a query cylinder with old phase a
and outside roots t_p has exact numerator

    C(d,a,J,t)=sum_(x=a mod d)
                  product_(p not in J)r_p(x)
                  product_(p in J)1_{t_p in A_p(x)}.

Thus its probability under the ONE actual uniform survivor source is C/Z.
The maximum mean of a free complete divisor query is the sum, over its
distinct numerical slots (d,J), of max_(a,t) C/Z. Each slot has its own free
query phase; all these phase choices can be made together and define one
query on the fixed source. Source phases are never selected again.

For saturated core faces S, sum only slots whose old p-exponent is at its
cap for every p in S. The resulting exact mean is beta'_S. The all-height
core transport gives positive actual surviving mass when

    lambda=sum_(nonempty S) beta'_S product_(p in S)1/(p-1)<1.

The query boundary must retain both r_p(x) and the root membership masks
{x:t in A_p(x)}. Cardinalities alone do not determine maxima of common-root
intersections across old rows. A complete algorithm intersects these masks
for each queried outside subset and takes weighted sums over old cylinders.
Duplicate intersection masks can be merged without changing any C value.
This is exact elimination on the declared interface; it is not a claim of
small state complexity for arbitrary incidence networks.

## The fixed71-original family and its source

The old315 originals are

    (3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
    (21,0),(35,0),(63,0),(105,0),(315,0).

They leave exactly102 old points. For each p=11,13,17,19,23 add0modp.
List the eleven nonunit315 divisors in increasing order asd_j, j=0,...,10.
Add exactly one original modulo p*d_j whose fixed CRT phase satisfies

    a=2 mod d_j,  a=1+(j mod(p-1)) mod p.

There are71 distinct odd nonunit numerical moduli and no original with
two outside primes. All phases are chosen once. These fixed actual
originals give102 old315 survivors,
pure zero roots at11,13,17,19,23, and55 singleton-outside mixed originals.
Its actual survivor count is45951340, and its actual retained fraction is
135151/228096, below the [fixed marginal method](746-saturated-query-laws-and-the-common-event-obstruction.md)'s exact threshold
for its sufficient estimate,46049941717/63611412480. This disproves that particular uniform
retention-only repair, but does not make the actual marked budget fail.

The exact formula above gives the following FULL outside-bearing caps:

| Saturated core S | beta'_S |
|---|---:|
|3|2634657/4595134|
|5|48930659/45951340|
|7|5864109/9190268|
|3,5|3567201/22975670|
|3,7|232547/2703020|
|5,7|7391271/45951340|
|3,5,7|62491/2703020|

Consequently

    lambda=101900963/147044288=0.692995045139...<1.

These are sharp separate query-mean maxima on this same actual source.
They include ALL32 subsets of the five outside cofactors; they are not
old315-only readings. The formula evaluates all384 full divisor slots.

At13,17,19,23 the root12 is universally allowed over every old survivor,
so it maximizes any queried outside coordinate. At11 all ten live roots
are tested explicitly. A second algorithm retains every intersection of
all root membership masks, without this universal-root simplification;
its maxima agree in all384 slots. Both computations use integer numerators
and exact rational division by the same45951340 denominator.

For this fixed shallow original family, add any finite distinct original
moduli with at least one higher3/5/7 exponent, keeping outside exponents
at most one and adding no other primes. Their phases may be arbitrary and
globally fixed. Uniform higher-core lifting and the exact partial caps give
actual Haar survivor density at least

    [45951340/(315*11*13*17*19*23)]*(1-lambda)
      =5015925/118982864>0.

This application fixes the shallow family. It does NOT prove the same
bound for arbitrary shallow phases or inventories, arbitrary additional
SHALLOW originals bearing multiple outside primes, higher outside exponents,
or unbounded prime support. The permitted higher-core originals may already
bear any subset of the five outside primes. The
unrestricted Erdős#7 problem remains unresolved. It does demonstrate a
specific missed relation: the mass-only envelope fails on a real source,
while its actual marked-cylinder boundary supplies a successful all-height
continuation on that very source.

The original uniform-source contract permitsN=102 here because the five
nonpure7 originals are redundant with0mod7. The auxiliary pruning used
by the later actual-source catalogue may instead choose a smaller source;
this counterexample does not rule out improvements using that different
source-selection rule.

## Exact consumer and proof boundary

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_marked_boundary.py)
and [result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_marked_boundary.json)
reconstruct all71 globally fixed CRT phases, the actual fibre incidence,
the source denominator and every query maximum. The first calculation
uses the four universal outside roots and all ten11-roots. The second
keeps every root-mask intersection. All384 slot maxima agree exactly.
It also recomputes the seven fixed-profile retention thresholds and
verifies the displayed positive all-height density.

An independent implementation reconstructed the71 originals and all
root intersections without the universal-root shortcut. It reproduced
all384 numerator maxima and the same debit and Haar lower bound.
The consumer pins the earlier partial and core-interface results;
it does not rerun their D2 arguments or turn the ordinary all-height
transport into a newly compiled Lean theorem. The [core-height transport](744-core-height-convex-transport-and-the-joint-fibre-boundary.md)
supplies that conditional all-height inference.

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_actual_marked_boundary.py
```
