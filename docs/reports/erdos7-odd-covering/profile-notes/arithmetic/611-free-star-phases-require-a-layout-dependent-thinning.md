# Free star phases require a layout-dependent thinning

For the cap-and-screen functional of
[Report608](608-one-common-thinning-frees-every-central-pair-role.md),
no single thinning matrix can give a positive gate for every star-phase
layout, even on one finite orbit of globally consistent actual families.
Every family in that same orbit nevertheless has its own positive thinning,
with gate greater than3/500 and complete ten-prime survivor Haar mass
greater than1/8700 under the inherited remaining-original conditions.

The obstruction keeps Report604's exact pure3/pure5 source and central15
phase0. All80 positive unmasked central leaves of the displayed family
are strictly inside the required Shearer region. Failure therefore comes
from requiring one common thinning across layouts; it is not caused by
an empty slice, a failed strict-region test or absence of a survivor.

This is an exact rational certificate for a specific sufficient method.
It does not rule out layout-dependent thinnings, stronger actual-source
estimates or noncoverage. It is ordinary mathematics, not new Lean
verification.

## 1. The family class and the same transformation everywhere

Let Lambda be the class of actual original families with the same numerical inventory and remaining-original conditions as608, with the exact pure3/pure5 restrictions and central15 phase0 retained, but arbitrary globally fixed phases at3q,5q,15q,3q^2,5q^2,9q,25q and all120 pair labels. Every other admitted mixed original may also have any globally fixed residue. Each numerical modulus is present at most once. Missing originals and the auxiliary pure deletions are retained under the same rules as before.

Use the following finite group G of coordinate transformations:

* At3, permute the three mod9 leaves0,3,6 inside mod3 root0; fix every other mod9 leaf and every other first root. Carry the higher digits along unchanged inside the exchanged subtrees.
* At5, independently permute the five mod25 leaves in each full root0,1,3, permute the four live mod25 leaves7,12,17,22 in root2 while fixing its excluded leaf2, and optionally exchange entire roots1 and3. Fix root4. Again carry higher digits along in the exchanged subtrees.
* At every outside prime, use the identity.

This is a finite subgroup of actual rooted p-adic-tree automorphisms. Its order on the positive central leaves is6*120^3*24*2=497664000. The transformations preserve product Haar, the exact ternary source (uniform on365 residues modulo729), the exact quinary root-balanced source, and all fixed pure originals. They fix the central15 class0. They map every p^e cylinder to another cylinder at exactly the same height and preserve numerical moduli.

For absent or source-null star labels one should use their actual zero activation, or transport any auxiliary padding choice as part of the layout. Reassigning a null9q label to a preferred named live leaf after every transformation could break equivariance. The obstruction criterion below needs only the orbit of one fully specified positive-leaf layout, so this optional padding issue can also be avoided by working entirely in that invariant subclass. Pair root padding to row0,column0,point(0,0) is already fixed by this group.

For one g in G, transform every actual original residue, every reference/query cylinder and every record by that SAME g. Central3 rows remain literal; quinary roots1 and3 move simultaneously in all labels. Prime identities are never exchanged. The result g lambda belongs to Lambda. The inverse transformation belongs to G, so this action is a bijection on Lambda. The assertion remains true with arbitrary finite original heights and Haar tails: the chosen rooted-tree maps are compatible at every height, not merely permutations of current leaf names.

The pure/source conditions are necessary here. One may not use a swap of ternary roots0 and1, arbitrary quinary root permutations, independent permutations at each q, or a permutation of numerical outside primes.

## 2. The functional and the mask condition

For a fixed lambda, compute the star factors b_q^lambda(l,m), the actual globally fixed padded pair cap profiles beta_e^lambda(l,m), and the fixed central15 mask. Let A_lambda(l,m) be the chosen strict-region indicator, for example the indicator that all b_q are positive, the relevant matching polynomial is positive and all required derivative brackets are positive. The same formula must be used for every family. It must depend only on that cell's transported b/beta values and the fixed outside graph, not on arbitrary residue-name choices or on theta.

Then

    A_(g lambda)(g b)=A_lambda(b),
    G_T^(g lambda)(g b)=G_T^lambda(b),
    H_T^(g lambda)(g b)=H_T^lambda(b),              (E1)

where G and H include the layout-dependent strict mask. The outside support T is unchanged because G fixes the numerical outside primes. Excluded strict cells have zero chosen source mass and zero chosen query grid; the construction does not require every cell to survive.

For theta in [0,1]^80, zero-extended to the masked/source-null cells, take the exact same certified bound

    K_lambda(theta)=(1-c)sum_b m_b theta_b H_empty^lambda(b)
       -sum_j tau_j max_(s in S_j)
                      sum_b s_b theta_b H_(T_j)^lambda(b),
    tau_j=(1-c)L_j+cW_j>=0.                         (E2)

Each K_lambda is concave in theta: its first term is linear and every debit is a nonnegative multiple of a maximum of linear forms. This remains true with family-dependent masks as long as the masks are fixed before theta.

E2 must be the actual full finite selector functional. Replacing it by an auxiliary optimization whose output is not concave, or selecting a mask by a theta-dependent rule without proving concavity, would require a new argument. Likewise a label-dependent heuristic mask is not automatically equivariant.

## 3. The complete selectors, including higher digits, transport correctly

The finite query modes retain the actual source masses at height0, each first-root fibre at height1, each individual leaf at height2, and the shared higher-cylinder density references at higher heights. A transformation in G merely permutes the corresponding finite selector family:

* Current source masses are constant on each transported orbit.
* First-root selectors stay fixed at3, and roots1/3 are swapped together at5.
* Singleton leaf selectors move to singleton leaf selectors.
* The ternary deep cap d3/2 is unchanged, and the quinary deep cap3*d5_j/5 is unchanged or transported from root1 to3, whose density references are equal.

Thus every S_j is taken bijectively to itself. The full analytic higher-height coefficients L,W depend on numerical exponents, outside primes and retained numerical labels; these are unchanged. All the query maxima are taken on the same transformed actual source and transported family, not on independently chosen laws. From E1 and this selector correspondence,

    K_(g lambda)(g theta)=K_lambda(theta),          (E3)

where (g theta)(g b)=theta(b).

## 4. The eight orbits

Positive ternary leaf indices split into

    R0={0,1,2}, R1={3}, R2={4}.

Positive quinary leaf indices split into

    C0={0,1,2,3,4},
    C1={5,6,7,8,9,15,16,17,18,19},
    C2={11,12,13,14}.

The product R0 x C0 is the fixed central15 mask. The other eight products are exactly the G-orbits. In lexicographic (R,C) order after removing(0,0), their sizes are

    30,12,5,10,4,5,10,4,

which sum to80. The action on each product is transitive. Averaging theta over G is therefore simply the arithmetic average of its coordinates within each of these eight blocks. This also agrees with source-mass averaging within an orbit, because the actual product source mass is constant there.

## 5. Averaging does not weaken a universal common witness

Define theta_bar=|G|^-1 sum_(g in G)g theta. For every actual lambda, concavity and E3 imply

    K_lambda(theta_bar)
      >=|G|^-1 sum_g K_lambda(g theta)
       =|G|^-1 sum_g K_(g^-1 lambda)(theta).         (E4)

If K_lambda(theta)>=gamma for every lambda, the right side is at least gamma. Hence a universal common witness with any prescribed margin gamma exists in80 coordinates if and only if one exists in the eight orbit coordinates. Equivalently,

    sup_(theta in[0,1]^80) inf_lambda K_lambda(theta)
      =sup_(theta in[0,1]^8) inf_lambda K_lambda(theta).        (E5)

There is a slightly stronger necessity statement relevant to a zero optimum. Suppose there is theta with K_lambda(theta)>0 separately for every lambda, even without a common positive infimum over this infinite class. For any fixed lambda, E4 is an average of finitely many strictly positive numbers, so K_lambda(theta_bar)>0. Thus positivity for every layout can also be assumed eight-block symmetric without introducing a uniform-margin assumption.

The same result already follows on the finite G-orbit of any particular actual lambda. No numerical enumeration of the497664000 group elements or all actual original heights is needed.

## 6. A concrete exact obstruction criterion

Suppose one actual layout lambda_* satisfies

    max_(eight-block theta in[0,1]^8) K_(lambda_*)(theta)<=0. (E6)

Since theta=0 is allowed, the maximum is then exactly0. An exact LP dual or finite rational convex combination of selected-query payoff vectors can certify E6. A floating zero optimum, unsuccessful search, negative evaluation at one theta, or positive result at a finite collection of layouts does not certify it.

E6 rules out every layout-independent common theta for E2 on the complete arbitrary-star/arbitrary-pair class. Otherwise average that common theta and apply E4 at lambda_* to contradict E6. Concretely, it is enough that the class contains the entire G-orbit of lambda_*.

An input lambda_* must be realizable by one fixed set of actual central residues. The arbitrary phases at distinct numerical star and pair labels can be completed by CRT with any fixed admissible outside residues; the same completion must be retained throughout. A mere cellwise selection of unrelated phase profiles is not an actual layout. The uniform cap functional need not be attained by its actual outside events, so E6 is a limitation of this certified cap/mask/selector construction, not a claim that every actual survivor law of lambda_* has nonpositive true gate.

This obstruction does not rule out theta_lambda chosen separately for each layout, a different actual-source construction, refined pair/phase estimates, a different equivariant mask with stronger results, or noncoverage itself. In particular a nonsymmetric positive theta for lambda_* can coexist with E6: its group transforms apply to different layouts in the orbit and do not form one universal witness.

## 7. One complete actual family

Take the fixed pure3/pure5 originals

    2 mod3, 7 mod9, 4 mod27, 13 mod81, 40 mod243, 121 mod729;
    4 mod5, 2 mod25,

and the five pure originals0 modq, q=7,11,13,17,19. Include the156
mixed labels from Report604: central15, all35 retained stars and all120
retained pair labels. Thus the explicit input has169 original classes,
with distinct odd numerical moduli. Its central15 residue is0.
Every other original is absent in this concrete input.

The central components of its stars are:

|q|3q and3q^2 mod3|5q and5q^2 mod5|15q point|9q mod9|25q mod25|
|---:|---:|---:|---|---:|---:|
|7|0|1|(0,1)|1|22|
|11|0|2|(0,2)|6|17|
|13|0|3|(0,3)|0|8|
|17|0|3|(0,3)|3|18|
|19|0|3|(0,3)|3|3|

Complete the q-components of3q,5q,15q,9q,25q by1,2,3,4,5 moduloq,
respectively. Complete3q^2 and5q^2 by1 and2 moduloq^2. These are chosen
once for the family.

At each outside pair, use one aligned central role for all three exponent
types(1,1),(2,1),(1,2), with code32R+8C+4I+J. In lexicographic numerical
pair order the ten codes are

    (9,11,9,9,27,18,18,27,27,27).                   (E7)

Their profile is1+rowR+columnC+point(I,J). Complete both outside components
of every pair original by1 modulo its indicated prime power. The
certificate gives the resulting169 literal residue classes and verifies
every CRT component and numerical modulus.

The higher-height inventory and query coefficient arrays used by K remain
the complete inherited arrays, not just the empty continuation of this
particular169-class input. Consequently a positive witness below proves
noncoverage also after adding any admitted remaining originals: on the
first seven primes they satisfy maximum exponent at least3, or both central
exponents at most1, or at least five prime divisors; originals touching23,29
or31 are unrestricted. Additional central-square labels or arbitrary
pure3/pure5 phases are not included.

The generalized star factor used for this family is

    b_q=1-r_q(1_(i=R1)+1_(j=C1)+1_((i,j)=(I,J))
                    +1_(l=L9)+1_(m=M25))
          -a_q(1_(i=R2)+1_(j=C2)),
    r_q=1/(q-1), a_q=1/[q(q-2)].                    (E8)

Here L9 and M25 use the same leaf indices as Report604; the table above
states actual residues. This is a cap on the union of the family's seven
star originals. The outside phases stay those of the one actual CRT input.
All mass, remaining-original deletions and query estimates are formed on
its one chosen actual source.

For the actual pair profiles in E7, exact evaluation yields

    min b_q =31/70,
    min Z_all =16645755587143/51448319523237>0,
    max_e sum_(f disjoint e)u_f =1334996/3338979<1.   (E9)

Thus all80 positive unmasked cells have a valid conditional pair-survivor
construction. Every family in its G-orbit has the same strict-region
values, up to cell permutation. No layout-dependent strict-cell deletion
is required on this orbit.

## 8. An exact dual bound on all eight-block thinnings

For theta that is constant on each of the eight orbits, write its
coordinates as x in[0,1]^8. Selecting one actual query selector for each
of the511 nonunit query rows gives a linear payoff

    F_sigma(x)=(1-c)mass(x)-sum_j tau_j Q_(j,sigma_j)(x).

Since each actual screen is a maximum,

    K_lambda*(x)<=F_sigma(x).                      (E10)

The data stores eight complete legitimate selector tuples sigma_h. Their
positive convex weights have common denominator2^24 and numerators

    (1607217,154258,4764971,251967,
     3466456,1255757,3320423,1956167).

They sum exactly to2^24. If g_h is the eight-coordinate coefficient vector
of F_(sigma_h), exact calculation gives

    d=sum_h weight_h g_h,
    d_j < -1/30000 for every j=1,...,8.              (E11)

No maximizing-selector or optimizer assertion is needed for these tuples:
they are complete menu entries and E10 holds for every x. Averaging E10
and applying E11 proves

    K_lambda*(x) <= d dot x
                  <= -(1/30000)sum_j x_j <=0.

At x=0 the gate is0, so the eight-block maximum is exactly0. By E4, there
cannot be any single80-cell theta with positive K on every actual layout
in this finite orbit. This includes the weaker requirement of separate
strict positivity without a common margin.

The dual pertains to the declared cap-and-screen functional. It does not
claim that the conservative caps are simultaneously attained by the
actual outside events, or that the actual survivor law has no positive
mass or no stronger certificate.

## 9. The same family has a positive layout-dependent witness

The data also stores one80-entry matrix with denominator2^24. Direct
exact evaluation of the full screens gives

    K_lambda*(theta_*)=
      6608889507256895066355100676316901171
      /1081295906642648549481711686123520000000
      >3/500.                                     (E12)

The complete23/29/31 continuation therefore gives Haar mass at least
(2673/138320)K_lambda*(theta_*), which is greater than1/8700.
For any g in G, E3 transports this same value to the family g lambda_*
using g theta_*. The matrices may differ between families; each family's
one matrix still serves both its mass and all its queries.

Accordingly this actual orbit separates two quantifier statements:

    for every lambda in G lambda_*,
      there exists theta_lambda with K_lambda(theta_lambda)>3/500;

    there does not exist theta such that
      for every lambda in G lambda_*, K_lambda(theta)>0.       (E13)

No contradiction is involved. The successful construction retains the
layout-dependent relation between source, star roles and thinning.

## 10. Reproducible certificate and boundary

The [producer](../../frontier/cover-geometry/star_common_theta_obstruction.py)
and [data](../../frontier/cover-geometry/star_common_theta_obstruction.json)
use only the Python standard library. Run

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/star_common_theta_obstruction.py

The producer pins Report604's source and producer, reconstructs all80
strict-region mass/query grids, all complete query menus, all eight dual
payoffs, the positive80-cell witness and all169 actual originals. The
source, coefficients, star roles, pair roles and selectors are shared by
the negative and positive certificates. No optimizer, floating sign test,
local search or independent per-cell phase choice is a proof input.

All18 named predicates, evaluated7311 times, pass under-O with explicit
failure branches. The finite arithmetic verifies E7--E12. The source
transport and finite averaging argument E1--E6 establishes the full
common-thinning obstruction, without enumerating the group orbit.

The result directs the arbitrary-star problem toward layout-dependent
thinnings or improved actual-source estimates. It does not prove that
every arbitrary-star layout has a positive witness: E12 covers the stated
finite orbit, and unrestricted star layouts remain a separate obligation.

[Report613](613-arbitrary-star-and-pair-phases-leave-a-retained-core-survivor.md)
shows that, under the same fixed central source and15 mask, all35 star
and120 pair phases can vary arbitrarily while the retained156-label core
still leaves positive mass. This does not pay the full continuation gate.
