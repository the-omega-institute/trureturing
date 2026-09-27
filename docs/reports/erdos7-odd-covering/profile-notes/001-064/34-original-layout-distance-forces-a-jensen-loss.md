[Index](../../marked_head_profile.md) · [Previous](33-retained-and-removed-original-events-control-convex-costs.md)

<a id="original-layout-distance-forces-a-jensen-loss"></a>
### Original layout distance forces a Jensen loss

On the same actual AP(4,6) probability and the same original labels as
[the preceding result](33-retained-and-removed-original-events-control-convex-costs.md),
retaining the distance between two original ternary test layouts gives

    Gamma357 <=1730443/48600 =35.605823045267...,
    Gamma13 <=18612601765191482089/121507008625163304
             =153.181301850738...,
    T13(81) <=2902346539226714392249430670150858799
              /29323692504044387688082860944928000
             =98.976161983229...,
    F17^-(403;nu13)+F19^-(403;physical mu17)
      <=52354504615418065873228931809032920671762399
          /119201303588774515306488246978221033433600
       =439.210839472299... .                         (LG1)

The joint improvement over the preceding439.673529721869 bound is
0.462690249569726... . All original heights, independent residues and
complete tails remain. These are ordinary mathematical inequalities
with exact rational checks, not Lean results or an unrestricted #7
resolution. The previous inequalities remain valid.

#### Shallow labels force a quantitative distance

Use the raw pure3 survivor measure eta, with the same five cells,
cell masses eta_l=w_l/9 and root labels (0,0,1,1,1). Each depth-a
ternary cylinder has eta mass at most3^-a. A complete ternary test B
has a shallow baseline

    b_l=1+1_(root(l)=r)+1_(l=j)

and a nonnegative integral-valued deep contribution H from depths
at least3. The union supporting H has eta mass at most

    sum_(a>=3)3^-a=1/18.

For two original ternary tests B=b+H and B'=c+H', put delta_l=b_l-c_l,
p=max(0,max_l delta_l) and q=max(0,max_l(-delta_l)). Then

    integral_eta (B-B')^2
       >=d_eta(b,c)
        :=sum_l eta_l delta_l^2-(p^2+q^2)/18.          (LG2)

Indeed, on delta_l>0 the value delta_l^2 can decrease only on the
support of H'; the total deduction is at most p^2/18. On delta_l<0
only H can cause a decrease, at cost at most q^2/18. The zero-delta
cells contribute a nonnegative square. The two support budgets are
separate; no assertion about their overlap is needed. Every deep
residue remains arbitrary.

For the ten displayed baselines, d_eta(b,b)=0, and distinct baselines
satisfy d_eta(b,c)>=1/18 throughout the original width simplex
w_l=1-u_l, u_l>=0, sum_l u_l<=1/2. This follows by checking the six
width vertices in the explicit affine formula (LG2). The bound uses
the raw measure, without any probability normalization factor.

If a shallow ternary indicator lies in a pure3 forbidden cell, move
that original test indicator to a surviving root or cell while keeping
its original5 residue. This changes the entire test and increases it
pointwise on the pure3 carrier; it does not just change its displayed
baseline. Establish the bound for that dominating complete test and
then return to the original one. Distinct original moduli remain
separate, including modulus15,45 and the higher five-labelled tests.
If the period lacks a required test coordinate, first lift to a larger
finite period and complete the test there; the old forbidden family
and its actual probability lift unchanged, and the extended test
dominates the original one.

#### An integer curvature bound controls the actual comparison loss

For a source cost f let the original zero7 cost be

    psi(v)=sum_(n>=1) p_n [f(nv)-f(n)]/n,
    p_1=29/35, p_n=36/(5*7^n) for n>=2.

Assume psi(k)-m*k^2 is convex on all integers k>=1, with m>0. Discrete
convexity, applied to the integer midpoint B0+B1, gives

    psi(B0+B1)
      <=[psi(2B0)+psi(2B1)]/2-m*(B0-B1)^2.            (LG3)

Here B0 is the same original zero5 ternary block of the selected
zero7 test, and B1 is its first positive5 ternary block after removing
only the five-coordinate factors. They need not have matching roots,
cells or deep residues.

The raw pure5 cap comparison groups these blocks only inside its
auxiliary nested intervals. At every actual ternary point, each
original5-labelled indicator still has its own5 residue and its own
cap. Replacing these indicators by nested intervals is an upper
comparison for increasing convex costs, as in the preceding section;
it does not identify the original congruence conditions. Its N5=2
interval has length1/5-1/25=4/25. Retain (LG3) on just that interval.
All other N5 values keep their existing complete comparison.

For a shallow baseline c, let

    A_c= sum_l eta_l psi(2c_l)
          +max_l sum_(a>=3)3^-a
              [psi(2(c_l+a-2))-psi(2(c_l+a-3))].

The existing arbitrary-prefix bound gives integral_eta psi(2B1)<=A_c.
Consequently the old first-positive5 contribution

    (2/25) max_c A_c

can be replaced, with the same original B0 baseline b, by

    (2/25) max_c[A_c-2m*d_eta(b,c)].                  (LG4)

The saving is the difference of these two expressions within the
same source comparison. It couples the norm and distance of one
actual first-positive5 block before maximizing it. A layout with a
small distance can have a smaller norm, and a norm-maximizing layout
can have a positive forced distance.

The previous removed-J5 loss V and cap-shrink loss(1/5-h)A remain
valid. Their chain is

    actual <= pure product -V
           <= nested(h)-V
           <= nested(1/5)-V-(1/5-h)A
           <= Jensen bound -V-(1/5-h)A-LG4 saving.

Thus these deductions occur at different steps. The same actual
retained-event/six-cofactor deletion argument still pays for the
original J5 overlaps. The Jensen deduction is not subtracted from
an independently maximized deletion term.

#### Complete curvature and tail identities

For f(v)=v^2, psi(v)=(6/5)(v^2-1), so m=6/5.
For the five quadratic AP tuple costs Q_(e,f), take the same auxiliary
counts N11,N13 from AP(4,6), and an independent N7 with the law p_n.
Write K=N7*N11*N13 and retain the event N11>e,N13>f. Then

    psi(v)=E[1_active*((K^2*v^2-16)_+-(K^2-16)_+)/K]
          =A*(v^2-1)
             +sum_(k=1..3)(p_k/k)*[(16-k^2*v^2)_+-(16-k^2)],
    A=E[1_active*K], p_k=Pr(active and K=k).           (LG5)

This is an identity with the full infinite tail. For every v>=4 the
finite positive-part terms vanish, leaving an exact quadratic
polynomial. The integer curvature is therefore the minimum of the
second differences centered at2,3,4 and the exact tail coefficient A.
No curvature claim is extrapolated from a finite numerical sample.

| AP tuple | Positive integer curvature m | Final normalized357 cost bound C |
|---|---:|---:|
| (0,0) | 27/26 | 2735335288798727/71898009183000 |
| (0,1) | 35/78 | 50628620561/4149957240 |
| (0,2) | 259/5070 | 4717107731/3252506400 |
| (1,0) | 49/110 | 41266885651/3403456056 |
| (2,0) | 217/3630 | 359419531/211701600 |

All final constants exceed their actual f(4), so the previous
unclipped cost floors and six-cofactor cap apply without modification.
For the tail of A_c in (LG4), isolate its depth3 increment. At depth4
and above both arguments of psi are at least4, and the tail is exactly

    4A*sum_(a>=4)3^-a*(2a+2c_l-5).

The verifier evaluates this complete geometric moment, not a cutoff.

#### Fixed norms on the full continuous domain

For each selected b, replace only its zero7 source summand by (LG4)
and leave all other original7 blocks unchanged. Let S_new be that
source bound, and let W(C) be the preceding six-cofactor signed cap.
Check

    C*s-S_new-W(C)/5>=0.                              (LG6)

The source f(v)=v^2 uses C=1730443/48600. The five other C values are
in the table. They are fixed on the entire original parameter domain.
The checker directly evaluates1296*10 source-square margins and
1296*10*5 quadratic margins, all nonnegative. The two inherited
missing3/effective9 source bounds5273/258 and14543/438 are smaller
than the new square constant.

The continuous extension is unchanged in form. Both A_c and
 d_eta(b,c) are affine in the width variables. Expanding the original
N5=2 summand first cancels its old maximum exactly; the replacement
is a positive multiple of a maximum of affine branches. All other
source and deletion terms retain their separate convexity. Thus
(LG6) is separately concave and its complete product-vertex check
extends to every original parameter point. One does not infer this
by subtracting two unrelated convex maxima.

#### Same-law propagation

The complete degree-two AP complement is still158957/1104246, and
the AP parent expectation remains2739361/28710396. Therefore

    H16=2739361/28710396+sum_(five tuples) C
                      +(158957/1104246)*(1730443/48600-1)
       =91360817781676601/1294164165294000
       =70.594457976605... .                          (LG7)

H41 remains the preceding complete linear-cost bound

    34223534699968380911680651169693124683
      /218275404408935878292461743570000000.

Every C and H16 bounds a cost under the normalized actual357 law.
D times such a bound is only an algebraic normalization numerator.
The actual AP survival bound remains Delta/D. Hence the same law gives

    Gamma13<=16+H16*D/Delta,
    F17^-+F19^-<=C0+(AC*H16+H41)*D/Delta,
    max D/Delta=708640143750/364671177293.

The square-hinge81 calculation keeps its old complete remainder and
replaces G357 in its exact degree-two complement. Direct1296-vertex
checks give (LG1); all three continuous-extension coefficients are
positive. The eight other branches are reconstructed with complete
geometric tails and remain below the stated targets. No input
probability or initial AP threshold is changed.

The same large finite core retains its error allowance0.000667,
so its sufficient joint threshold becomes

    403-T13(81)-0.000667=304.023171016770... .

The new439.210839472299 joint bound remains135.187668455529... above
that threshold. The uniform negative-Q condition and continuation
through arbitrary later primes remain open.

#### The former parameter vertices cannot simply be discarded

The six former controlling parameter vertices lie in the closure of
actual forbidden families. For one representative use surviving
ternary cells1,4,2,5,8 modulo9, forbid0 modulo3 and7 modulo9, and
write a cylinder by its low digits first. For depths a>=3, pure3
exclusions in cell1 follow a string of2 digits ending in0; mixed
3^a5^e exclusions in that same cell follow the same2 spine ending
in1. The two collections are disjoint. In the five coordinate use
an all4 spine whose final digit is0 for pure5,1 for3*5^e,2 for9*5^e,
and3 for all deeper mixed labels. Put the3*5^e labels in root2
modulo3 and the9*5^e labels in cell2 modulo9.

For finite exponent heights A>=3 and B>=1 put

    x=sum_(a=3..A)3^-a, y=sum_(e=1..B)5^-e.

The exact original parameters are

    1-w=(9x,0,0,0,0), alpha=(0,y), beta=(0,0,y,0,0),
    late=(xy,0,0,0,0), z=1-y.

They approach vertex398 as A,B grow. Permuting the surviving
ternary siblings gives the other five vertices. This establishes
parameter feasibility in the closure, without asserting that an
actual complete test attains any comparison maximum. The strict
improvement comes from retaining a joint test observation, not from
removing admissible parameter limits.

#### Exact verification

[The verifier](../../verify_layout_gap_frontier.py) binds its mathematical
source, both predecessor certificates, [the final norm inputs](../../certificates/layout_gap_norms.json)
and [its component](../../frontier/cover-geometry/layout_gap.py) by SHA-256. It checks
all77760 final norm margins, the full curvature/tail identities,1296
consumer vertices and eight complete missing-class branches against
[the result certificate](../../certificates/layout_gap_frontier_certificate.json).
The source laws, original modulus labels and finite-core error terms
are unchanged. These checks accompany the ordinary argument above;
they do not constitute Lean verification.
