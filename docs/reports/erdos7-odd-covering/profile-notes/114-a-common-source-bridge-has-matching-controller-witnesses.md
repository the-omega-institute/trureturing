[Index](../marked_head_profile.md) · [Common mean and hinge source](109-the-mean-and-all-hinges-share-one-original-test.md) · [Compatible factorial head](112-the-factorial-tail-retains-one-compatible-original-head.md)

# A common source bridge has matching controller witnesses

The surviving factorial head and the shallow part of its positive-seven
cross term can be placed inside109's same source LP. This gives a
pointwise stronger operator than separately applying112's cell caps.
For every one of the ten positive quadratic cost generators of113,
however, its exact uniform maximum is unchanged. A matching source LP
witness proves this equality for each generator.

Consequently this refinement gives zero additional numerator or
comparison gain. All52 retained cost bounds and the full111 denominator
remain those of113, and the complete face comparison remains

    C0+N/d<=459.139828574756367119... .              (JS0)

The result closes this particular source refinement with an explicit
obstruction. It does not establish optimality of the true cost, an
actual covering family attaining a source LP, or failure of every
possible richer source constraint.

The scope is the two entire actual saturated K faces, with r=rho=0,
D=53/360, all independent original test labels and complete infinite
tails. There is no off-face extension, new global K, Lean verification
or unrestricted Erdos #7 resolution.

## 1. Keep the surviving head and shallow cross term as source functions

Use112's fixed head ell, load B, functions Phi,h4, density w, and raw
source Lambda. Let G=I3*I9*I5*I15. It is zero when the four original
head residues are incompatible; otherwise it is the fixed45 rectangle
(c9,s5). The indicator I45 keeps its own original rectangle(c45,s45).

Define the nonnegative source function

    L_ell=w*Phi(B)+(6/5)*(I45+G).                  (JS1)

The first term comes from the surviving factorial head. Its complete
forced27 deduction is

    K27(ell)=q_s/135

when all six head indicators are compatible and their rectangle is in
cell1, and zero otherwise. Here q=(0,1/5,1/5,3/20,1/5), as in75 and112.
Thus

    integral_mu Phi(B)
       <=integral_Lambda w*Phi(B)-K27(ell).         (JS2)

The factor6/5 in(JS1) comes from the six shallow old labels with
0<=a<=2,0<=b<=1, paired with all original positive seven depths. For
any fixed head45 rectangle, intersection with each such old label
is either empty or the entire rectangle. Bound its complete
positive-seven family by(1/5) times the actual Lambda mass of that
rectangle. There are six distinct old exponent pairs. Applying the
pointwise inequality h4(B)<=I45+G gives precisely the second term
of(JS1). No surviving w is applied to this raw positive-seven cap.
The original positive-seven residues can be different for every label.

For each fixed rectangle define the remaining complete raw row

    Drow(c,s)=p(c,s)/9+3*d(c,s)/20
                                 +I_(d(c,s)>0)/360. (JS3)

These are the same three deep exponent regions of112. Define

    R_ell=O(w*h4(B))
            +[Drow(c45,s45)
                 +I_(G compatible)*Drow(c9,s5)]/5
            -K27(ell).                            (JS4)

Here O is112's complete old-tail operator. With the unchanged complete
pair tail P_TT<=2539/3600, the same-original-test bound is

    T5(A)<=integral_Lambda L_ell
                              +R_ell+2539/3600.    (JS5)

The old and seven geometric series in(JS3),(JS4) are complete. The
pair term retains all old-old, old-seven and seven-seven pairs with
their distinct original labels. Applying the finite factorial
inequality first and then monotone convergence proves(JS5) for the
complete original test A.

## 2. One LP may integrate both source functions

For one exact nonnegative expansion

    f(v)=a+sum_t c_t*h_t(v)+theta*Phi(v),
    a>=0, c_t>=0, theta>=0,

write109's fixed-layout lower-hinge bound as

    K_c+LP(F_(ell,xi))+S_(ell,xi)-c1*C(ell).        (JS6)

The selected positive-seven root and slot are xi. K_c contains its
complete peeled old and complementary seven tails. S contains its
selected-label operators, still acting on their original independent
labels. C is109's proved mean-head deletion correction. The LP has
exactly the same three source groups, cell caps and group mass bounds
as in109.

Adding(JS5) before taking the source bound gives

    integral_mu f(A)
      <=a*D+theta*(2539/3600)
        +max_(ell,xi)[K_c+LP(F_(ell,xi)+theta*L_ell)
                       +S_(ell,xi)-c1*C(ell)+theta*R_ell]. (JS7)

The mean correction is multiplied only by c1. The factorial forced27
correction is contained in R and multiplied only by theta. Both apply
to their proved positive cost functions. There is no additional
independent deletion credit and no substitution of C for K27.

The raw cross estimate in(JS1) is uniform in xi. Thus it can be added
to the same actual source integral even though109 retained only its
original selected positive-seven projections. Different quadratic
costs still have independent complete tests.

## 3. The new operator is dominated by113 at every layout

Write R(c,s) for112's raw source cell caps, and J(ell) for its factorial
head operator. The definitions give the exact identity

    sum_(c,s) R(c,s)*L_ell(c,s)+R_ell=J(ell).       (JS8)

All coefficients of L_ell are nonnegative. Every feasible source
allocation lambda satisfies0<=lambda(c,s)<=R(c,s). Consequently

    LP(F+theta*L_ell)
       <=LP(F)+theta*sum_(c,s)R(c,s)*L_ell(c,s)    (JS9)

for theta>=0. The shared source group constraints are preserved in
both LP terms. Combining(JS8),(JS9) proves that(JS7)'s operator is
at most113's operator for each fixed ell,xi. Its uniform maximum
therefore cannot exceed the corresponding113 maximum.

The checker verifies the positive coefficients and exact(JS8)
decomposition on all12500 independent head layouts. This is a
repartition of the existing source upper bound, with its complete
remainder, rather than a replacement of source geometry by a new
probability law.

## 4. Matching source allocations give the reverse inequality

For each of the ten positive quadratic generators, the old maximum
has head

    ell=(0,1,2,0,2,1,2).                          (JS10)

At this head, L_ell is16/5 on the single source cell(c,s)=(1,2)
and zero everywhere else. Its raw cell cap is1/45. The exact common
LP optimizer already fills this cap. The checker constructs a
feasible source allocation and a matching dual for the new combined
objective. It also verifies that the allocation pays the lower-hinge
LP and the entire factorial source cap simultaneously, so(JS9) is
an equality at the controlling witness.

For all ten generators, the new value at this explicit witness equals
its complete113 maximum. This supplies the reverse inequality to
Section3 and proves equality of the two uniform maxima. A second full
quadratic enumeration is unnecessary for this conclusion.

The shared maxima are:

| Cost index | Complete candidate upper bound |
| --- | ---: |
| 41 | 321941926743947/60932432310750 |
| 42 | 1947338600947/1342863522000 |
| 43 | 46111593947/268572704400 |
| 44 | 592378506773/360546936750 |
| 45 | 579333736109/2523828557250 |
| 47 | 1296144121/388962000 |
| 48 | 7289003/1852200 |
| 49 | 39800437/9261000 |
| 50 | 1040606353/231525000 |
| 51 | 5341922/1157625 |

These are candidate operator maxima. Index47 retains its stronger
existing cost bound. Index46 remains outside this positive expansion:
its four middle hinge coefficients are negative, so substituting upper
hinge bounds would reverse the needed direction. All final per-cost
minima and majorants remain those of113.

This obstruction identifies a specific missing restriction: keeping
the source of the current two head functions identical is insufficient,
because the relaxed source LP can already maximize both at the same
controller. The result makes no claim that every feasible LP allocation
arises from an actual source family.

The helper `frontier/whole_quadratic_same_source.py` exports
`JointFactorialSource`, which builds(JS7) with exact primitive scaling.
Its certificate retains the ten matching primal/dual witnesses,
all-layout source decomposition digest, full signed52-cost numerator
and unchanged complete denominator. Both additional gain fields are
exactly zero.
