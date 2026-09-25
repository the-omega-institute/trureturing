# Arbitrary central pure phases admit two complete boundary gates

The prescribed pure3/pure5 inventory can be removed from both
[Report617](617-all-central-star-phases-admit-root-one-continuation.md)
and [Report623](623-a-common-matching-source-admits-arbitrary-edge-endpoints.md).
Every actual pure3 or pure5 original may now have its own arbitrary fixed
residue and arbitrary finite height. The central15 residue is arbitrary
as well. One actual supported source supplies the mass and every query.

The two endpoint interfaces have different certified margins:

| Outside interface | Complete raw gate lower bound | Ten-prime Haar lower bound | Outside network consequence |
| --- | --- | --- | --- |
| Report617 fixed root-one layout | 534185412720319/23749451159961600 > 11/500 | >1/1900 | Exactly Report616's network leaves >1/2100 extendible head mass |
| Report623 arbitrary per-edge endpoints, possibly colliding linear stars | 135228904182589/189995609279692800 > 7/10000 | >1/59000 | This smaller gate does not pay Report616's full fee |

Both bounds use the complete remaining-original and all-height query
inventory. They are ordinary proofs with exact integer certificates, not
new Lean verification. The mixed-label and endpoint conditions specified
below remain restrictions; unrestricted Erdős #7 is not settled.

## 1. Family, source and endpoint scope

Let P0={3,5,7,11,13,17,19}, Q=P0\{3,5}, and P1={23,29,31}.
The family is finite, its original numerical moduli are distinct, and each
original has one residue fixed for the whole family. All pure originals
on P0 are now arbitrary at their own finite heights. No maximum height is
fixed uniformly across families. The prime set itself remains this fixed
reference set; there is no arbitrary-head-prime transfer.

Retain the35 star labels, seven at each q in Q:

    3q,5q,15q,9q,25q,3q^2,5q^2.

Retain the120 pair labels, twelve at each edge{q,r}:

    3^a5^b q^i r^j,
    (a,b) in{0,1}^2, (i,j) in{(1,1),(2,1),(1,2)}.

All central star/pair residues are arbitrary and globally fixed. Missing
retained slots may be imposed as auxiliary deletions. Every other mixed
P0-original must satisfy at least one of

    maximum exponent >=3;
    v3<=1 and v5<=1;
    support cardinality >=5.

The retained35+120 labels are removed once from the remaining loss inventory.
Originals touching23,29 or31 are unrestricted. The complete512-entry L/W
arrays are those of
[Report604](604-fixed-pair-activation-admits-ten-central-square-stars.md).
The pure3/pure5 classes are handled by the source construction, not charged
again as mixed originals. Original numerical labels are never merged or
duplicated by any subsequent relabelling.

There are two alternative outside interfaces:

* **Root-one:** keep Report617's outside first-root layout. Its five
  linear-star roots are distinct, its square-star components are arbitrary
  lifts at the corresponding first and second star roots, and every pair
  label projects to the first star root at both outside coordinates.
  Pair higher lifts are arbitrary. The rootwise construction only uses
  square-cylinder caps and the first-root rectangle, so these higher
  choices do not change its response. The formerly prescribed central
  pure phases and central15 are released as proved below.
* **Matching:** use Report623's interface. Linear-star live roots may
  coincide. Each square star projects to its corresponding3q or5q root,
  with arbitrary higher lift. The twelve labels on each edge share one
  endpoint root at each coordinate, but those roots may differ between
  edges incident to the same prime. Pair higher lifts are arbitrary.

In particular the matching result does not yet allow twelve independently
chosen endpoint pairs within one edge, or square-star roots independent
of their corresponding linear-star roots.

## 2. Construct the actual pure sources before taking numerical corners

Write H_p for normalized p-adic Haar. Equivalently, work in a finite
resolving quotient large enough for the originals and any finite set of
queried cylinders, with height at least2. The densities constructed below
depend on finitely many original digits; extend them constantly through
any additional free digits. These compatible extensions define the same
source for all finite queries and do not change the original family.

At3, delete the actual pure3 root, or one auxiliary first root if absent.
Of the six remaining mod9 leaves, delete the actual pure9 leaf if live;
if absent or already source-null, delete one auxiliary live leaf instead.
Delete all actual higher pure originals. Their total Haar cost is at most

    sum_(e>=3)3^(-e)=1/18.

The actual remaining mass is at least

    1-1/3-1/9-1/18=1/2.                                  (AP1)

Each of the five nonnull leaves has positive surviving Haar mass: its
mass before higher deletions is1/9, greater than the entire1/18 tail.
Twice the surviving leaf masses give capacities at most2/9 whose sum
is at least1. Choose masses w_l below them summing to1 and constantly
thin2H_3 within each actual surviving leaf. This realizes one probability

    rho3<=2H3, supported on every actual pure3 original's complement.

For fixed null leaf z, the numerical leaf vector satisfies

    w_z=0, 0<=w_l<=2/9, sum_l w_l=1.

Put d_l=2/9-w_l on the five nonnull leaves. Then d_l>=0 and sum d_l=1/9.
Consequently w is the convex combination with weights9d_l of the five
vectors having one weakened leaf of mass1/9 and four leaves of mass2/9.
There are6*5=30 ordered choices of null and weakened leaf.

At5 perform the corresponding first-root, one live square-leaf, and all
actual higher-pure deletions. The higher tail is

    sum_(e>=3)5^(-e)=1/100,
    1-1/5-1/25-1/100=3/4.                                (AP2)

The nineteen nonnull capacities under(4/3)H5 are at most4/75 and sum to
at least1. Constant thinning realizes rho5<=(4/3)H5 with actual leaf
masses v_m. Their deficits4/75-v_m sum to1/75. Thus v is a convex
combination of nineteen vectors with one weakened mass3/75 and eighteen
masses4/75. Including the null position gives20*19=380 source corners.

These probability sources are constructed on the actual surviving sets
first. The numerical corner vectors need not be realizable on that same
family's higher-digit survivor. They will only be used in a separately
concave lower estimate for the actual source; they are not substituted
for its high-digit law.

## 3. Normalize the actual or auxiliary central15 and classify twenty sources

If the actual15 event has live endpoints after the first pure deletions,
keep it. If absent or already source-null, impose any live auxiliary
root rectangle instead. Relabel its two live roots to0 and the two deleted
pure roots to2 at3 and4 at5. Apply the same rooted-tree bijections to the
whole family, all reference leaves and all queries. Cylinder heights,
Haar mass and numerical moduli are preserved. A source-null original15
is already avoided and is not reintroduced as another numerical original.

The selected central deletion is now the root rectangle(row0,column0).
One cannot instead send an already deleted original endpoint to a live
root while fixing the pure deletion; the auxiliary rectangle is necessary
in precisely that case.

Index the six live mod9 leaves by0..5 with row l//3, and the twenty live
mod25 leaves by0..19 with column m//5. Fix row0 and column0. Independent
leaf permutations inside roots and permutations of the three other
quinary columns classify the30*380 corners into the following20 types:

    THREE=((0,1),(0,3),(3,4),(3,0));
    FIVE =((0,1),(0,5),(5,6),(5,0),(5,10));
    CASES=THREE x FIVE.

Each pair denotes(null,weakened). The four ternary orbit sizes are
6,9,6,9, summing to30. They record the null row and whether the weakened
leaf is in the same row. The five quinary sizes are20,75,60,75,150,
summing to380: null column0 with weakened same/other; null elsewhere
with weakened same/column0/another nondistinguished column. The indicated
groups act transitively in each case, so these invariants are complete.
All template roles and query menus are transported together.

## 4. Full-height selectors and separate concavity

The exact root and square masses are w and v. For every higher cylinder,
the actual sources satisfy

    rho3([a]_(3^e))<=2*3^(-e),
    rho5([a]_(5^e))<=(4/3)*5^(-e).                       (AP3)

The unchanged L/W arrays already include the geometric height sums and
their reference normalizations. In their four central statuses, the new
selector menus at3 are

    w; w restricted to a row; w_l delta_l; delta_l.

At5 they are

    v; v restricted to a column; v_m delta_m; (4/5)delta_m. (AP4)

The final selectors in AP4 are constant density caps at a nonnull leaf,
not the leaf mass multiplied by that cap. In particular they are not
w_l delta_l or(4/5)v_m delta_m. Null queries give zero. Include the zero
selector when evaluating signed comparison grids. The sixteen central
menus are the tensor products of these one-coordinate menus.

Fix one actual family and make all needed auxiliary star deletions once.
In the root-one case use Report617's actual rootwise submeasure. In the
matching case use Report623's actual star-union survivor, uniformly thinned
to its scalar lower mass Z, then condition and scale using its strict
matching-polynomial region. The latter construction permits colliding
linear-star roots because union-bound overpayment cannot insert a forbidden
configuration. It still uses the two square-to-linear root anchors.

At every central leaf either construction supplies one actual outside
submeasure and all32 simultaneous support-query grids H_T. The conditional
construction depends on that leaf's activation flags, but not on its
weight w_l or v_m. Mixing it with the already constructed actual central
source gives the complete gate

    K(w,v,H)=g sum_(l,m) w_l v_m H_empty(l,m)
       -sum_j c_j max_(s in menu_j(w,v)) sum_(l,m)s_lm H_(T_j)(l,m),
    g=1-c, c=1084133/201247200,
    c_j=(1-c)L_j+cW_j>=0.                                (AP5)

Every grid vanishes on the fixed central15 rectangle. AP5 lower-bounds
eta(1)-c Gamma(eta) for the same actual complete-core survivor eta after
all remaining mixed originals have been deleted.

For fixed null positions, every member of each selector menu is affine
in w with v fixed, and affine in v with w fixed. In particular the deep
selectors are constant, hence affine. The maximum over each fixed menu
is convex in either block. The mass term is affine in either block.
Therefore K is separately concave, and successive convex decomposition
gives

    K(w,v,H)>=sum_(i,j)lambda_i mu_j K(w^i,v^j,H).         (AP6)

No joint concavity in(w,v) is asserted. No unsupported corner law is
declared to be the actual source. A uniform lower bound over the numerical
corners bounds the response of the actual source already fixed above.

The five outside aligned-response comparisons of Reports617/623 remain
separately affine before applying this concave gate. Fix theta=1 for all
seven blocks; apply the two source comparisons and five outside comparisons
successively. Their corner construction then requires a uniform estimate
for every one of the20 central source cases and every five-template layout.

## 5. The new source stabilizers preserve joint template and query data

For source(null3,weak3,null5,weak5), a template is

    (R,C,I,J,L,M),
    R in{0,1}, C in{0,1,2,3}, (I,J)!=(0,0),
    L a nonnull ternary leaf, M a nonnull quinary leaf.

There are2*4*7*5*19=5320. The positive unmasked central domain has80,83,85
or87 cells, depending on the source. At each such cell the uniform means
of I_C, I_P+I_L+I_M and1-I_R are respectively

    1/4, 1/7+1/5+1/19, 1/2.                              (AP7)

Hence both the root-one mean(A,B) and the matching mean Z, and all their
local signed-pair interval arrays, are unchanged. The source weights and
query selectors are changed. The previous80-cell, denominator58400 and
317920-orbit source metadata are not a certificate for these new cases.

For a fixed new source, permute regular leaves within each root, fixing
the null and weakened markers. Ternary rows stay fixed. Permute quinary
columns only while fixing column0 and the pair of marker-containment
indicators of each column. This one common source-preserving action acts
on both ordered templates, all cells, and the entire query menu.

An ordered pair of leaves is classified by its two regular/weak groups and,
within one group, by equality versus inequality. Its orbit size is
|G||H| for different groups, |G| for equality, or |G|(|G|-1) otherwise.
This gives10 or11 ternary leaf-pair orbits and29 quinary ones. Normalize
the inner leaf pair, apply every permitted outer column permutation, and
renormalize. Taking the least key of this finite list gives the full
declared stabilizer orbit because the inner group is normal under those
column permutations. The distinct normalized outer images are disjoint
inner orbits of equal size, proving the multiplicity formula.

The full ordered-template orbit is the product of the four fixed(R,R')
choices, the ternary leaf-pair orbit and the quinary partial-template
orbit. The twenty representative counts are:

| THREE \ FIVE | (0,1) | (0,5) | (5,6) | (5,0) | (5,10) |
| --- | ---: | ---: | ---: | ---: | ---: |
| (0,1) |159560|462640|462640|462640|909440|
| (0,3) |175516|508904|508904|508904|1000384|
| (3,4) |159560|462640|462640|462640|909440|
| (3,0) |175516|508904|508904|508904|1000384|

The sum of orbit sizes in every case is5320^2=28302400. For each prescribed
central column pair(C,C'), the weights sum to1330^2=1768900. Each representative
fills only column entries reached by one common permitted permutation.
The final stored witnesses are transported template pairs actually having
those columns, not merely the representative's original IDs.

The independent finite orbit check enumerates every one of the532^2
quinary partial-template pairs for all five quinary sources, and every
ternary leaf pair, recovering exactly these orbit fibres. Covariance of
source weights, activation indicators and all selectors proves that the
same pair value can be used throughout each such orbit.

## 6. Complete directed arithmetic for both interfaces

Use each reference proof's exact signed-pair integral identity, which
contains every interaction degree through five. At each pair take its
lower mass grid and upper query grids with sign-aware interval rounding.
Superadditivity of AP5 bounds its actual five-template gate below by the
sum of these ten pair contributions. Pair-table minimizers are allowed
to disagree on other roles because they give lower bounds, but one shared
column is retained for each of the five prime blocks. Minimize the sum
over all4^5=1024 common column choices.

All corner selectors have denominator dividing675=9*75. Their integer
source weights are0/1/2 over9 and0/3/4 over75; the deep factors are9
and60 in those numerators. Every selector has total mass at most1.
If local interval scale is Hs, each integer screen has absolute value
at most2*Hs*675. With coefficient scale Cs, the pair budget is bounded by

    (2*Hs*675)(ceil(Cs*g)+sum_j ceil(Cs*c_j)).             (AP8)

The producer and kernel check AP8 fits signed64 for screens and that
10000*10 times the pair bound is below2^120 for signed128 budgets and
final rational comparisons. Root-one uses Hs=2^21,Cs=2^24; matching uses
Hs=2^23,Cs=2^27. Gain/coefficient rounding reverses correctly for negative
mass or query screens. No floating-point value enters the proof.

For each model, the complete scan evaluates10319064 ordered-template-pair
representatives over ten outside edges:103190640 evaluations, followed
by20480 common-column assignments across the20 sources. Both uniform
minima occur at source case12=(3,4,5,6). They are exactly

    gamma_root=534185412720319/23749451159961600 >11/500,
    gamma_match=135228904182589/189995609279692800 >7/10000. (AP9)

The finite scan covers the comparison boundary parameters, not a cutoff
on original or query heights. AP1--AP3 and the complete analytic L/W sums
supply the all-finite-height statements.

Independent reconstruction checks all84480 interval entries for each
model, all source/template state arrays and pair column masks, all3200
generic-selector table witnesses per model and all shared-column minima.
The source, convexity and orbit arguments above are ordinary mathematics;
none of these checks is represented as a Lean kernel proof.

## 7. Project to Haar and pay only the network justified by each margin

Both actual core sources have full Haar density bounded by

    D=2*(4/3)*product_(q in Q) q/(q-2)
      =13832/2025=(4/5)*(3458/405).                       (AP10)

The unchanged23,29,31 head kernels have conditional density multiplier
200/33, giving

    C=110656/2673, alpha=1/C=2673/110656.                 (AP11)

Thus the root-one ten-prime head lower bound is

    alpha*gamma_root=52884355859311581/97334046946544844800
      >1/1900.

The matching lower bound is

    alpha*gamma_match=1912523073439473/111238910796051251200
      >1/59000.                                         (AP12)

Even the simpler gamma_match>7/10000 gives a head bound>1/60000.

Each head singleton cap is still at most2; the core pair caps are at most
14/5<10/3, while the whole-head pair cap4 is valid. Actual conditional
head-kernel bounds5/3,20/11,2 are unchanged. Consequently the root-one
version supplies exactly the same joint source interfaces for
[Report616](616-three-parent-entries-with-two-outside-parents-preserve-a-common-survivor.md).
Its full fee remains bounded by

    fee616=1/780+4/125000+1/65536+2(1/250000+1/1600)
          =20665363/7987200000.

The resulting extendible head mass is at least

    alpha*(gamma_root-fee616)
      =76051760909347958229/158167826288135372800000
      >1/2100.                                         (AP13)

For an actual allowed finite outside network the full density is greater
than1/(2100 Q_off), where Q_off is the product of the actual outside
resolving prime powers.
This uses Report616's fixed parent tuples and declared ordinary private
interfaces; it is not a statement that every intermediate fibre survives.

The matching raw margin in AP9 is smaller than fee616. Its improved Haar
density cannot pay that raw deletion budget, so AP13 is not transferred
to the matching scope. Neither version inherits the larger approximately
0.0265 arbitrary-three-parent fee of Reports619/620. Any such extension
requires a new same-source estimate.

## Retained reproducible certificate

The [producer](../../frontier/cover-geometry/arbitrary_pure_source_certificate.py),
[integer kernel](../../frontier/cover-geometry/arbitrary_pure_source_certificate.cpp),
[source orbit generator](../../frontier/cover-geometry/pure_source_template_pair_orbits.py)
and [complete data](../../frontier/cover-geometry/arbitrary_pure_source_certificate.json)
contain both complete20-case scans, actual transported witnesses, common
column minima, source pins, and explicit675-denominator arithmetic bounds.
The producer always runs both complete scopes; intermediate output is
marked incomplete. It regenerates the two pinned local interval sources
but imports only their coefficient/interval suffixes, rebuilding every
source-dependent part of the new inputs.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_pure_source_certificate.py

No optimizer output or scratch path is an input. The proof's remaining
restrictions are the fixed prime set, mixed-label inventory and the stated
endpoint relations. The next missing interface is not hidden by the
positive margins in AP9.
