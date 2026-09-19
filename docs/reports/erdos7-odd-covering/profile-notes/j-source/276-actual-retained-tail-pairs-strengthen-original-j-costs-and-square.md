[Index](../../marked_head_profile.md) · [Previous complete comparison](275-generalized-factorial-observations-improve-the-complete-j-comparison.md) · [Generalized factorial crosses](274-generalized-factorial-thresholds-strengthen-two-original-j-costs.md) · [Complete raw prime paths](265-complete-raw-prime-paths-improve-the-positive-seven-pair-block.md)

# Actual retained tail pairs strengthen original J costs, square and Phi5

On both entire actual saturated J faces, the following complete integral
bounds hold for the unchanged original functions:

| Target f | Factorial threshold | Exact upper for integral f(A)dmu | Decimal prefix |
| --- | ---: | ---: | ---: |
|cost-48|3|402172082863385623/113400000000000000|3.54649103054131942680776014...|
|cost-49|2|3045114520043616887/793800000000000000|3.83612310411138433736457545...|
|square|1|17653307900058777407/3969000000000000000|4.44779740490269020080624842...|
|factorial5|5|4552688500270367/5670000000000000|0.80294329810764850088183421...|

Their improvements over the corresponding complete target bounds in275
are

    cost-48: 0.09642066009847090753338372... ,
    cost-49: 0.08427344417563593852355757... ,
    square: 0.08470259509730979919375157... ,
    factorial5: 0.04469559078124038800705467... ,

Each target retains all62,500,000 original containing choices, the whole
late interval and every omitted prime/cofactor depth. The model remains
3306 variables,6354 inequalities and18 equalities. The objective now uses stronger bounds for all three parts of the
omitted distinct-pair expansion. These source inequalities require a
separate consumer to update the full52-cost comparison.

## The original whole-load identities are unchanged

Write H_t(n)=(n-t)_+ and Phi_k(n)=(n-k)_+*(n-k+1)_+/2.
For positive integers n,

    cost48(n)=5*H_3(n)+2*Phi_3(n),
    cost49(n)=(31/16)*H_2(n)+(17/16)*H_3(n)+2*Phi_2(n),
    n^2=1+H_1(n)+2*Phi_1(n).                            (JP1)

The first two functions are respectively(n^2-9)_+ and(n^2-81/16)_+.
The square is the original outside-square function, not another index
in the52-cost inventory. Its exact constant, linear and quadratic tail
coefficients are(0,0,1); the helper checks them in addition to every
finite transition. A finite sample is not used as the proof of(JP1).
The fourth target is the unchanged original Phi5 observation. It has
at-one constant zero, factorial coefficient one and an empty hinge sum;
its polynomial for n>=5 is(n^2-9*n+20)/2. Neither the square nor Phi5
adds another cost index or a new scalar observation.

Keep the original six-label head B=1+I3+I9+I5+I15+I45 and let
A=B+O+Z, where O contains all omitted zero-seven labels and Z all
positive-seven labels. For h=(B-k+1)_+,274 gives

    Phi_k(A)<=Phi_k(B)+h*O+h*Z+binom(O+Z,2).             (JP2)

At k=1 and k=2 this is equality for every possible B and every
nonnegative integer tail. At k=3 only B=1 uses the monotone-binomial
case; at k=5 the cases B=1,2,3 use it. The complete factorial crosses h*O and h*Z retain274's actual
X/Y/V objective, full residual series and convex common-theta secant.

The remaining distinct-pair term has three disjoint parts:

    binom(O+Z,2)=binom(O,2)+O*Z+binom(Z,2).              (JP3)

The previous complete cap was4879/7200. In the present objective each
replacement below removes only known assigned cap-series payments,
then adds a valid bound for those same actual pairs. No diagonal or
independently optimized saving is subtracted from an unknown moment.

## Fifteen retained old-old pairs use actual survivor counts

Let

    D={25,27,75,81,135,125},
    M=sum_(d in D) I_d.

All six labels belong to O. The original cap of a compatible old-old
pair is Csurv(lcm(d,e)); incompatible classes have empty intersection.
Writing m=3^a*5^b outside the original six-label head, the inherited
complete survivor caps are

    Csurv(m)=11/(20*3^a)                 if b=0,
             13/(30*5^b)               if a=0,
             1/(3*5^b)                 if a=1,
             1/(9*5^b)                 if a=2,
             1/(3^a*5^b)               otherwise.      (JP4)

The15 distinct pairs in D have the exact assigned payment

    C_OO=sum_(d<e in D) Csurv(lcm(d,e))=8857/202500.     (JP5)

Replace this subseries by the actual integral of binom(M,2).
If m is the population count of the original four-bit25/27/75/81 mask,
and n in{0,1,2} is the number of retained135/125 events, then

    binom(m+n,2)=binom(m,2)+m*n+binom(n,2).              (JP6)

Thus, for a factorial coefficient f, add f*binom(m,2) to the actual
survivor Y column and f*(m*n+binom(n,2)) to its V state, then remove
f*C_OO from the outside constant. The three explicit V states have
n=1,1,2; the unretained state has n=0. Intersections retain their actual
multiplicity, including135 and125 simultaneously.

The entire remaining old-old cap is

    P_OO-C_OO=153919/1620000 >0.             (JP7)

All original old labels outside these15 pairs retain their complete
assigned cap series.

## Selected old-positive-seven pairs use the same actual raw source

Let Cr be258's raw cofactor cap, with no survivor density inserted.
The exact positive-seven depth weight is u_e=6/(5*7^e), and
sum_(e>=1)u_e=1/5. Select, for each d in D, all cofactor1 depths,
cofactors3,5,9,15 at depth1, and cofactors3,5 at depth2.
Their complete original assigned payment is

    C_OZ=sum_(d in D) [Cr(d)/5
         +(6/35)*sum_(c in{3,5,9,15}) Cr(lcm(d,c))
         +(6/245)*sum_(c in{3,5}) Cr(lcm(d,c))]
        =5402/91875 .                         (JP8)

The cofactor1 term includes every positive depth, not just the first two.
Each of the other selected terms has its own original modulus and
independently chosen residue. There are42 records in the certificate;
six are full infinite cofactor1 blocks and36 are single-depth terms.

Let m1_i count the actual21/35/63/105 projections at raw cell i,
and m2_i the actual147/245 projections. The retained mixed-pair bound is

    integral M*(1/5+(6/35)*m1+(6/245)*m2)dLambda.         (JP9)

The same raw X mask records its first four old indicators. The retained
U states record the additional135/125 indicators on Lambda. Accordingly
add f*m*(1/5+(6/35)*m1_i+(6/245)*m2_i) to X, and the same coefficient
with m replaced by n=1,1,2 to U. Remove only f*C_OZ from the outside
constant. This uses actual raw events; it does not replace raw mass by
a survivor-weighted marginal or identify independently selected residues.

The complete remaining mixed cap is

    P_OZ-C_OZ=481829/4410000 >0.             (JP10)

These replacements are disjoint from(JP5) and from all positive-seven/
positive-seven pairs. The original complete identity is checked exactly:

    P_OO+P_OZ+89/240=4879/7200.                          (JP11)

## Positive-seven pairs retain the known first two projections

For each positive-seven depth e, let F_e be its own complete original
old-cofactor load on the same Lambda. The original test residues may
vary independently with e and with every modulus. Existing compatible
seven-intersection bounds give

    P_ZZ<=sum_e u_e*integral binom(F_e,2)dLambda
          +sum_(e<f) u_f*integral F_e*F_f dLambda.       (JP12)

Applying2F_e*F_f<=F_e^2+F_f^2 allocates to each square the exact weight

    beta_e=((e-1)*u_e+sum_(f>e)u_f)/2
          =u_e*((e-1)/2+1/12).                          (JP13)

This is an identity for every positive integer e: the higher partner
sum is u_e/6. Its complete sums yield

    (u1,beta1)=(6/35,1/70),
    (u2,beta2)=(6/245,1/70),
    (sum_(e>=3)u_e,sum_(e>=3)beta_e)=(1/245,1/210).      (JP14)

For one original raw head H, use265's complete same-head upper bounds
P(H,theta) and Q(H,theta) for integral binom(F,2) and integral F^2.
They include both complete raw prime-path potentials and every omitted
pair and diagonal. Their uniform maxima are125/96 and53/16.

At depth1 the original21/35/63/105 projections fix five of the seven
raw-head coordinates, leaving25 complete head choices. At depth2 the
147/245 projections fix the root and slot, leaving1250 choices. Define

    L1(pi,theta)=max_(H extends pi) [(6/35)*P(H,theta)+Q(H,theta)/70],
    L2(pi2,theta)=max_(H extends pi2) [(6/245)*P(H,theta)+Q(H,theta)/70].
                                                               (JP15)

The pair and square terms in each bracket use the same complete head.
They are not separately maximized and then asserted to share an optimizer.
All later depths remain in the full constant

    C_later=(1/245)*(125/96)+(1/210)*(53/16)=31/1470.     (JP16)

For the six actual positive-seven projections,

    P_ZZ<=L1(pi,theta)+L2(pi2,theta)+C_later.             (JP17)

Each fixed-head P,Q bound is affine in theta. The maxima in(JP15) are
therefore convex, as is their sum. Its two endpoint values bound the
entire interval by the secant at the one actual common theta. Both
endpoint values are at most the old89/240 cap. In the original LP,
replace f*(89/240) by f times this secant: its endpoint difference is
added to column875 and its lower endpoint to the constant.

The checker reconstructs all12,500 raw heads at both endpoints using
265's original discounted-potential function. Its25,000 full-component
hash exactly matches265's existing certificate. It then reconstructs
500 first-projection rows,10 second-projection rows and all5000 joint
projection combinations, including every remaining raw-head completion.
No maximum of endpoints is interpreted as an attained actual source.

## One original objective combines every retained term

All additions in(JP6),(JP9),(JP17) share the same3306-variable model as
274's head, hinges and factorial crosses. X,U are actual raw states and
Y,V actual survivor states. The original constraints and the single
common late coordinate remain. Only column875 may have a signed price;
every supplied rational dual is checked in all3306 columns.

Each target has a fresh instance with k fixed before any cache is used.
At k=1, the square's exact mass term3/20 is included. Every original
complete two-, four- and six-projection affine pruning bound is recomputed
at the appropriate threshold, with its full old4879/7200 pair bound.
Those bounds remain valid for the same original function even though
the new LP uses stronger actual pair information. No hinge-only pruning
bound or cached value from another threshold is used.

Once all six positive-seven projections are fixed, refine each of those
three complete affine lines by the same endpoint correction

    delta_ep=f*(PZZ_ep-89/240)/scale.                     (JP18)

The correction is nonpositive at both endpoints. Each line originally
contains the full distinct-pair payment, so replacing its PZZ component
by(JP17) preserves a bound for the entire original cost. The checker
maximizes the minimum of the three refined affine lines over the full
late interval, testing both endpoints and every pairwise intersection.
Only branches remaining above the current largest bound require a
joint LP dual. The30 exact supplied seeds for each target initialize
this bound without an optimality assumption.

For the first three targets, the exact coverage equation is
500*n2+10*n4+n6=62,500,000:

| Target | n2 | n4 | n6 | Conditional-affine prunes | Joint-dual branches |
| --- | ---: | ---: | ---: | ---: | ---: |
|cost-48|124966|1061|6390|5716|326|
|cost-49|124952|693|17070|15751|579|
|square|124968|122|14780|14460|208|

Within n6, the original-affine prunes, conditional-affine prunes and
joint-dual branches are disjoint and exhaust the entire count.

The pure Phi5 target uses a separate scanner because its hinge sum is
empty. At a fixed old head, its original complete bound is the maximum
of the two old head-plus-cross endpoints plus4879/7200. This bounds
all5000 positive-seven projections. If this does not prune the head,
each projection replaces only the old89/240 PZZ payment by the two
complete conditional endpoints in(JP17). The maximum of this new affine
line remains a complete bound. Remaining branches use the minimum of
that complete affine bound and the exact joint-source dual bound.
No bound on a smaller hinge component is used.

The pure-Phi5 coverage equation is

    5000*12493 + 34813 + 187 = 62,500,000.

Its60 supplied seed branches are exactly checked to initialize the
largest certificate bound. The full scan then covers every original
choice; no optimality assumption about the seeds is used.

The maximizing certificate branches are

| Target | Original old-head layout |21/35/63/105/147/245 projections|
| --- | --- | --- |
|cost-48|(1, 4, 2, 1, 2, 4, 2)|(1, 4, 4, 1, 4, 1, 4)|
|cost-49|(1, 4, 4, 1, 4, 4, 4)|(1, 4, 4, 1, 4, 1, 4)|
|square|(1, 4, 2, 1, 2, 4, 2)|(1, 4, 4, 1, 4, 1, 4)|
|factorial5|(1, 4, 2, 1, 2, 4, 2)|(1, 4, 4, 1, 4, 1, 4)|

They maximize certified upper bounds, not necessarily actual covering
families. The four targets do not have to share an optimizer.

## Exact artifact and boundary

The [helper](../../frontier/j-source/j_face_joint_pair_factorial_heads.py) and
[certificate](../../certificates/source_norms/j-source/j_face_joint_pair_factorial_heads.json)
retain137 mathematical source pins,1359 exact rational duals and
4492854 checked domination columns across250000000 original choices.
There are50000 threshold-specific factorial/cross records,
100000 cross endpoints and57 independent original-affine compiler checks.
The complete POO/POZ assigned payments and complements, original265
raw-head components, conditional PZZ tables and branch decisions all
recompute with exact standard-library rational arithmetic. Only consumed
duals are retained using the existing canonical codec.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/j-source/j_face_joint_pair_factorial_heads.py --check
```

This proves ordinary complete source inequalities on both saturated
actual J faces. A full52-cost comparison, off-face extension, global
join, Lean verification and unrestricted Erdos7 resolution are not
established by this source artifact.
