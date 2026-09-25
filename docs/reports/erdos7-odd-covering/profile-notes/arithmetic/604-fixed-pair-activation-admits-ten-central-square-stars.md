# Fixed pair activation admits ten central-square stars on one source

Six explicit central activation patterns admit all ten labels9q and25q,
q in V={7,11,13,17,19}, together with the remaining original inventory of
[Report598](598-high-support-central-squares-preserve-the-common-survivor-law.md).
Under the precise phase and pure-source conditions below, the ten-prime
survivor has Haar mass greater than1/5000. Four patterns also admit all
ten labels9q^2 and25q^2 with arbitrary residues, giving mass greater
than1/5500. Every unspecified original phase and finite original height
remains arbitrary.

The four-pattern version can additionally admit the160 one-central support-four labels
of [Report603](603-two-support-four-slices-reduce-the-core-gap-to223.md)
and every separated Type I/II branch of
[Report601](601-staged-payment-admits-every-two-parent-entry-from37.md), with
entries from37 and arbitrary head-parent pairs. The extendible head mass
then exceeds1/11000; the full density exceeds1/(11000 Q_off).

This is a phase-restricted noncoverage class. It does not give a new
phase-unrestricted head bound or replace the global remaining-label count.
The proof reuses Report597's actual conditional pair-survivor construction,
retaining its fixed activation beta in both mass and query estimates.
The new work is an exact common-source certificate for the stated family,
not a new general Shearer theorem or Lean verification.

## Original family and all phase restrictions

First take the fixed head P={3,5,7,11,13,17,19,23,29,31}. Original numerical
moduli are pairwise distinct. Each allowed numerical label may be absent
or present once. All residues are globally fixed.

Pure3 and pure5 originals must be a subset of

    2 mod3, 7 mod9, 4 mod27, 13 mod81, 40 mod243, 121 mod729;
    4 mod5, 2 mod25.                                 (FA1)

No other pure3 or pure5 class is included in this theorem. Pure powers at
all other head primes are unrestricted. A missing FA1 class can be imposed
as an auxiliary deletion when constructing the source.

The15 original, if present, has residue0 mod15. Write

    j_7=1, j_11=2, j_13=j_17=j_19=3.

For each q in V, the retained star originals have these central components:

|Original label|Central component|
|---|---|
|3q, 3q^2|0 mod3|
|5q, 5q^2|j_q mod5|
|15q|0 mod3 and j_q mod5|
|9q|1 mod9|
|25q|12 mod25|

Every q-component of these originals is arbitrary. Their phases at
different numerical labels need not agree.

For every q<r in V retain all twelve pair labels

    3^a5^b q^e r^f,
    (a,b) in{0,1}^2, (e,f) in{(1,1),(2,1),(1,2)}.    (FA2)

For each outside exponent type, its four central activations are an
unconditional term, a row mod3, a column mod5, and a point(mod3,mod5).
Choose one of the following six tables for the entire family. Order the
ten pairs lexicographically by their indices in V, and number them
h=0,...,9. Number the exponent types(1,1),(2,1),(1,2) by t=0,1,2.

|Pattern|Row R|Column C|Point(I,J)|
|---|---:|---:|---|
|concentrated00|0|0|(0,0)|
|concentrated01|0|1|(0,1)|
|concentrated12|1|2|(1,2)|
|endpoint-star, pair q<r|0|j_r|(0,j_r)|
|cyclic|(h+t) mod2|(2h+t) mod4|((h+t+1) mod2,(h+2t+1) mod4)|
|separated|1|2|(0,(h+t) mod4)|

Thus the label3q^e r^f has central residue R mod3, the label5q^e r^f has
central residue C mod5, and15q^e r^f has central point(I,J). The120
numerical labels are distinct. Every outside q,r component remains
arbitrary. The certificate includes CRT examples with outside components0
to demonstrate simultaneous realizability; those components are not a
restriction in the theorem. Missing or source-null retained slots may be
padded using the same listed roles, only enlarging their upper estimates.

Every other mixed original on the first seven primes satisfies the
Report598 rule

    maximum exponent>=3, or v3<=1 and v5<=1,
    or at least five prime divisors.                 (FA3)

Every original touching23,29 or31 is unrestricted. The special labels are
retained once and excluded from the remaining-original debit. This is not
a superset of Report598's entire arbitrary-phase class: FA1 and the listed
central roles restrict phases, while the ten9q/25q labels enlarge its
numerical inventory. No assertion for arbitrary central pair roles is made.

## The actual pure source and its shared density references

Normalize Haar on the ternary survivor of FA1. Of the729 words exactly365
survive. Index its retained mod9 leaves by l=3i+t, representing residue
i+3t, i in{0,1}, t in{0,1,2}. Their masses and full density are

    w=(81,81,81,81,41,0)/365, d3=729/365<2.           (FA4)

On the quinary survivor use the actual root-balanced source. Index leaves
by m=5j+t, representing residue j+5t, j in{0,1,2,3}, t in{0,...,4}. Then

    v_10=0,
    v_m=1/16 for m in{11,12,13,14},
    v_m=1/20 otherwise;
    d5=(5/4,5/4,25/16,5/4) by first root.             (FA5)

These masses and density references come from the same finite pure
survivors. They are not independent extreme values. Their higher-digit
lifts preserve the stated density bounds at every query height.

For q in V use Report591's actual root-balanced survivor of all pure-q
originals. Write

    r_q=1/(q-1), a_q=1/[q(q-2)].

Its first-cylinder and second-cylinder upper bounds are r_q and a_q; its
height-e cap for e>=2 is1/[(q-2)q^(e-1)]. Its full density is at most
q/(q-2). The product source rho consequently satisfies

    rho<=D H_core, D=2*(5/3)*product_(q in V)q/(q-2)
                   =3458/405.                       (FA6)

It avoids FA1, all actual outside pure originals, and any chosen auxiliary
pure deletions. Changing the unspecified outside phases changes its actual
conditional laws, but does not change any of the uniform bounds used here.

## One fixed activation grid for the actual pair survivor

Delete the central root cell(i,j)=(0,0), even if the15 slot is absent.
At leaf(l,m), put i=floor(l/3), j=floor(m/5). The conservative star factor is

    b_q=1-(r_q+a_q)(1_(i=0)+1_(j=j_q))
          -r_q1_((i,j)=(0,j_q))
          -r_q1_(l=3)-r_q1_(m=12).                 (FA7)

Every b_q is positive. The actual star survivor fraction f_q is at least
b_q by one union bound. Thinning that actual conditional source by b_q/f_q
therefore gives central mass w_l v_m product_q b_q and a product conditional
outside law at the fixed leaf.

For e={q,r}, the three outside exponent types have weights

    r_q r_r, a_q r_r, r_q a_r.

Multiply each by its fixed activation1+row+column+point and sum to obtain
beta_e(l,m). This is a cap determined by the original central roles, not
an assertion that the union probability equals the cap. Put

    u_e=beta_e/(b_q b_r),
    Z_A(u)=1-sum_(e in A)u_e
              +sum_(e,f in A, disjoint, unordered)u_e u_f.   (FA8)

The dependency graph is the shared-coordinate graph of the ten pair
unions. Matchings on five outside vertices have size at most two.
For every one of the six patterns, all105 unmasked leaf cells satisfy

    Z_all(u)>0,
    max_e sum_(f disjoint e)u_f<1.                  (FA9)

These exact inequalities imply positivity of every induced polynomial:
each coordinate derivative is negative throughout the box below u, and
zeroing omitted coordinates can only increase Z. This supplies the strict
region required by Report597; checking Z_all alone would not suffice.

Use Report597 PS9--PS11 on the actual pair unions, with the same beta for
all queries. The chosen conditional pair-survivor submeasure is
Z_all(u) times the actual conditional avoidance probability measure.
It remains below the prior actual source. Define

    G_T=1_(central cell survives) product_(q notin T)b_q,
    H_T=G_T Z_(edges disjoint T)(u).                (FA10)

Equivalently H_T is the signed matching expansion with beta_e and
beta_e beta_f. H_empty is the exact mass grid of this chosen submeasure;
it need not equal the mass of the unthinned physical survivor. H_T is its
query upper grid for every outside support T at every height. Denominators
cancel exactly as in Report597. No new source or beta is selected by a query.

## Fixed rational thinning and complete-height query coefficients

For each of the six patterns the certificate provides one6-by20 matrix

    theta(l,m)=integer/2^24, 0<=theta<=1.

Multiply the chosen actual submeasure by this one matrix. Its mass grid
is theta H_empty and every query grid is theta H_T. These fixed weights
are sufficient witnesses; no claim of optimality is required.

The156 retained labels are15, the25 old star labels, the10 new9q/25q
labels, and the120 pair labels. Enumerate all remaining FA3 labels by
central statuses0,1,2,3, where3 means the complete tail of heights>=3,
and by their outside support T. This gives512 entries L_(e3,e5,T).
For an outside q, the original-height coefficient for status0,1,2,3 is

    1, r_q, a_q, 1/[q(q-1)(q-2)].

The central original-tail coefficients for status3 are1/9 at3 and1/60
at5; the other central statuses contribute coefficient1. Their actual
probabilities are supplied by the screens below.

The weighted nonunit-query array W uses central coefficients

    at3: (1,3,5,8/9), at5: (1,3,5,1/8),

and at each active outside coordinate the complete weighted series

    omega_q=3/(q-1)+(5q-3)/[(q-2)(q-1)^2].          (FA11)

The unit entry of W is zero. These are analytic geometric sums over
all heights, not a maximum-exponent truncation.

For each central coordinate a screen averages when it is absent, takes
a maximum over root-cylinder sums at status1, and a maximum over weighted
single leaves at status2. At status3 it takes the maximum leaf value
multiplied by d3/2 or, on quinary root j,3d5_j/5. Consequently the complete
actual original tails are d3/18 and d5_j/100; the complete weighted tails
are4d3/9 and3d5_j/40. The source masses in FA4--FA5 and these references
are used together in every screen S_(e3,e5).

With c=1084133/201247200, one actual supported submeasure therefore has
continuation gate at least

    K(theta)=(1-c)sum_(l,m)w_l v_m theta(l,m)H_empty(l,m)
       -sum_((e3,e5),T)[(1-c)L+cW]S_(e3,e5)(theta H_T).       (FA12)

This follows from the remaining-original union bound and the complete
query moment bound, including the unit term. The separate query caps are
upper bounds; their simultaneous attainability is unnecessary. Their
common actual source, beta, theta and original phases are retained.

## Exact gates and the ten-prime conclusion

Direct rational substitution of the fixed matrices into FA12 gives:

|Pattern|Exact gate, decimal display only|
|---|---:|
|concentrated00|0.0266093384212016...|
|concentrated01|0.0127880531254853...|
|concentrated12|0.0286164003849816...|
|endpoint-star|0.0113761793071543...|
|cyclic|0.0252455584091235...|
|separated|0.0264044885694416...|

The certificate retains exact fractions and verifies K>11/1000 in each
case. Applying the existing23,29,31 continuation afresh to the resulting
actual core source uses the same controls2/5,9/20,1/2 and density multiplier
200/33. The extended physical law is then restricted to its full head
survivor. Its mass-to-density estimate gives

    H_P(U)>=alpha K, alpha=33/(200D)=2673/138320,
    alpha*(11/1000)>1/5000.                       (FA13)

This holds for every unspecified outside phase and remaining-original
phase, and every allowed finite height, in the stated family.

## Four patterns admit ten further squares

For concentrated00, concentrated12, cyclic and separated, add all labels
9q^2 and25q^2, q in V, with arbitrary globally fixed phases. Since the
chosen source remains below rho, their simultaneous deletion mass is at
most

    B10=(max_l w_l+max_m v_m)sum_(q in V)a_q
       =(81/365+1/16)sum_(q in V)1/[q(q-2)]
       =6808439/454381200.                        (FA14)

The unit-inclusive query restriction lemma of Report598 charges at most
(1-c)B10 to the gate. For the four patterns the respective remaining gates
are0.0117060777797...,0.0137131397435...,0.0103422977677... and
0.0115012279280..., all strictly greater than1/100. Therefore their
complete ten-prime survivor has Haar mass greater than1/5500.

This clause is asserted only for those four patterns. It is not inferred
for the other two from failure or success of a separate sufficient bound.

## The160 one-central support-four labels and arbitrary separated entries from37

For these same four patterns one may simultaneously add all160 labels

    9 product_(q in S)q^e_q or25 product_(q in S)q^e_q,
    S subset V, |S|=3, every e_q in{1,2},

with arbitrary globally fixed phases. This is the one-central support-four
subclass in Report603. Its source bound also applies here because
max w<=2/9, max v<=1/15 and all outside caps agree. Its total raw mass is

    B160=(2/9+1/15)sum_(|S|=3)product_(q in S)(r_q+a_q)
        =2261681116741/813717439920000.            (FA15)

This inventory is disjoint from the156 retained labels and the extra ten
squares. Pay this deletion on the same source,
then apply Report601's early/late blocker payment, retaining exactly its
original branch-separation and private-block conditions.

The core source remains dominated by rho after every restriction. Its
complete pair marginals are bounded by10/3 times pair Haar, so early
blockers cost at most(10/3)S35<1/780 before continuation. Reconstruct the
23,29,31 kernels on that restricted source. After continuation use one
Haar submeasure on the head survivor to pay late blockers and Type I
branches. Their costs are S323<1/125000 and2^-17. No Type II private
descendant is charged twice.

Using only the already proved K_after10>1/100 gives the common sufficient
bound

    H_P(U_ext)>
      alpha[1/100-(1-c)(B160+1/780)]-1/125000-2^-17
      =1687238234614993717021/16948040294649784320000000
      >1/11000.                                  (FA16)

All restrictions and continuation steps use the same actual law. Distinct
entry primes may have overlapping head-parent pairs, while their private
interiors remain disjoint. Actual extension witnesses consequently glue
as in Report601. Full density exceeds1/(11000 Q_off), where Q_off includes
all outside prime powers and separate components. No uniform full-density
constant independent of Q_off is claimed.

This corollary remains subject to FA1 and the fixed central roles. It does
not lower the phase-unrestricted remaining-label count. It does not permit
cross-entry originals or arbitrary recursively shared two-coordinate
separators.

## Reproducible exact certificate

The [producer](../../frontier/cover-geometry/actual_pair_activation_certificate.py)
and [data](../../frontier/cover-geometry/actual_pair_activation_certificate.json)
use only the Python standard library. The six fixed dyadic matrices are
explicit data in the producer. It reconstructs the finite pure sources,
all156 retained labels, the512 complete-height loss and query coefficients,
actual fixed-role CRT examples, each beta and H grid, every screen and all
positive gate inequalities. Strict-region checks are exact at every
unmasked cell. The160-label cap is rebuilt by literal enumeration and an independent
geometric-product formula. Inherited continuation and branch inputs are
fingerprinted;
no inherited full head scan is rerun.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/actual_pair_activation_certificate.py

All106 named predicates, evaluated43317 times, pass. Every check uses an
explicit failure branch and remains active under-O.
The data contains sufficient rational witnesses and consequences, without
optimization output or a dependency on any earlier negative-envelope
experiment. The conditional-law, complete-height and family-quantifier
arguments are the ordinary proof above; the arithmetic is not presented
as new Lean verification.
