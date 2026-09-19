[Index](../marked_head_profile.md) · [Broad slot tradeoff](85-a-broad-five-slot-source-deletion-tradeoff.md) · [Actual source domain](48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Common deletion transfer](57-common-deleted-measure-coupling.md)

# A clipped full-load interface on the broad slab

Use profile85's actual effective9 source, broad slab

    Delta=(z-3/4)+(1/4-alpha1)+(1/4-sum_(i>=2)beta_i)<=1/18,

and its small-best-slot-loss branch r<1/12000. Let H be the most
occupied first-five slot, and retain the same actual raw35 measure
Lambda, surviving marginal mu, original virtual deletion V and
actual projected deletion delta. All tests have arbitrary,
independently chosen original residues.

Write v3 and v9 for the densities of the complete original
cofactor3 and9 virtual families relative to Lambda. They are
exactly the shallow carrier marginals used in the old comparison;
each lies between0 and1/5. Define

    w_H=1-v3-v9-(1_H+1_(root1 intersect H))/5.

Then1/5<=w_H<=1. For every complete independently labelled old35
test A0, including the unit, the following full-load inequality holds:

    integral A0 dmu
       <=integral w_H*A0 dLambda
          +(17100/397)*[rho-(r+r1)/5]+T40,             (CL1)

where rho=S-S0 is the actual residual above the common-carrier
mass lower bound, r1=h1/5-Lambda(root1 intersect H), and

    T40=351520265979651248437376109626376737817577
          /58972439045013398092123679816722869873046875000
       <3/500000.                                    (CL2)

The bracket in(CL1) is nonnegative. No exponent tail has been
discarded. For a complete original357 test A, the same inequality
gives

    integral A dmu357
       <=integral w_H*A0 dLambda+(s+C)/5
          +(17100/397)*[rho-(r+r1)/5]+T40,             (CL3)

where s=Lambda(1), mu357 is the same actual full surviving measure,
and C is the complete raw35 nonunit cap sum of profile48.

This extends the bounded-head interface to the full identity
load. It does not bound the remaining weighted-source expression
by the old direction40 margin with a positive gain. That source
optimization remains open; no new global K bound, threshold403
result or Lean verification is claimed.

## 1. The complete load on a fixed five slot has a uniform cap

The actual measure Lambda is dominated by eta tensor five-adic
Haar measure. For original ternary test cylinders, the complete
sum of their uniform eta caps is at most

    h+h1+max_i eta_i+sum_(a>=3)3^-a
          <=5/9+1/3+1/9+1/18=19/18.                (CL4)

Here h1 is the larger root mass in the effective9 domain. A test
cylinder in a removed root or cell has mass zero. For every
five-coordinate test of depth b>=1, its intersection with the
fixed first slot H is empty or the entire depth-b cylinder.
At depth zero its intersection has Haar mass1/5. Thus the sum
of the five factors, including every depth, is

    1/5+sum_(b>=1)5^-b=1/5+1/4=9/20.

Expanding the original load into its nonnegative indicators and
summing these product caps proves

    integral_H A0 dLambda<=19/40,
    integral_(root1 intersect H) A0 dLambda<=19/40.    (CL5)

The different original test residues need not be nested, and the
individual intersection upper bounds need not be simultaneously
attainable. The nonnegative expansion and complete geometric sums
suffice. In particular(CL5) also applies to phi=min(A0,40).

## 2. Both selected families use one actual deficiency budget

Let V5,V15 be the full virtual cofactor5 and15 families, with
complete caps h/25 and h1/25. Put

    E5=h/25-V5(1), E15=h1/25-V15(1),
    omega=(V-delta)(1), g0=397/36000.

Profile85's source packing, including the wrong-root alternative
for cofactor15, gives bad-carrier weights q5,q15 satisfying

    E5>=r/5+g0*q5,
    E15>=r1/5+g0*q15,
    E5+E15+omega<=rho.                               (CL6)

An absent original label contributes its full missing capacity.
All seven depths have been summed with weights6/(5*7^e), whose
complete sum is1/5. Good labels use H for cofactor5 and root1
times H for cofactor15. Hence for any nonnegative phi,

    integral phi dV5 >=(1/5-q5)*integral_H phi dLambda,
    integral phi dV15>=(1/5-q15)*integral_(root1 intersect H) phi dLambda.

Apply this to phi=min(A0,40), and use(CL5)--(CL6). With

    c=(19/40)/g0=17100/397>40,

the selected virtual integrals have lower bound

    [integral_H phi dLambda+integral_(root1 intersect H) phi dLambda]/5
              -c*[E5+E15-(r+r1)/5].                  (CL7)

The exact relation mu=Lambda-V+(V-delta), restricted to
nonnegative observations, now gives

    integral phi dmu
       <=integral w_H*phi dLambda
             +c*[E5+E15-(r+r1)/5]+40*omega
       <=integral w_H*phi dLambda
             +c*[rho-(r+r1)/5].                      (CL8)

The last step uses c>=40 and the single budget(CL6). It does
not pay rho once per family. The cofactor3 and9 virtual measures
are retained exactly inside w_H, and all other virtual deletions
are discarded only in the direction valid for this upper bound.
Since E5>=r/5 and E15>=r1/5, the final bracket is nonnegative.

## 3. Restore the entire clipped tail by a dominating actual source

In the effective9 branch, keep the fixed forbidden source moduli3
and9 and remove every other source restriction. Up to the fixed
ternary relabelling of this branch, the resulting raw35 measure
Lambda_plus dominates every Lambda under consideration. Its five
cell data are

    d_plus=(1,1,1,1,1),
    n_plus=eta_plus=(1/9,1/9,1/9,1/9,1/9),
    s_plus=5/9.

These are source vertex1 in the established enumeration. This
domination follows by removing forbidden classes; it does not
require a monotonicity claim for a patched parameter table.
For every original test A0,

    integral(A0-40)_+ dmu
       <=integral(A0-40)_+ dLambda_plus
       <=raw35(40,data(vertex1))=T40.                (CL9)

The last upper bound is the established original-label zero-five
source operator. Its evaluator retains the complete ternary and
five-adic affine tails after their exact tail entrance. The value
in(CL2) is an exact evaluation of this operator, not a finite
load sample or a selected test realization.

Using A0=min(A0,40)+(A0-40)_+ in(CL8)--(CL9), and w_H>=0 to
replace min(A0,40) by A0 in the positive source integral, proves
(CL1). The complete positive-seven test labels have raw mass sum
at most

    sum_(e>=1)6/(5*7^e)*(s+C)=(s+C)/5.

Dropping actual mixed7 deletion on those nonnegative terms proves
(CL3). These labels are disjoint from the zero-seven label set;
their full original residues remain arbitrary.

## 4. The residual coefficient is usable, but the source comparison remains

The current signed global K comparison gives identity direction40
weight

    beta40=94212612766226/1174116234095805.

Its actual-mass coefficient from profile74 is strictly larger
than beta40*(17100/397). The checker verifies this with the
complete exact rational coefficients. Thus this particular
linear residual penalty can be absorbed by the existing mass
term if a valid net source comparison is established.

This coefficient comparison alone is not such a source comparison.
One still needs to bound

    integral w_H*A0 dLambda+(s+C)/5

jointly with the old conditional identity cost, retaining the same
source, H and independent test. Subtracting its apparent slot gain
from an old bound without checking existing payments would not
follow from(CL1). The additive T40 is also retained in every use.

## 5. Exact reproduction

The [checker](../frontier/broad_clipped_identity.py) verifies the
complete column factors, common transfer coefficient, dominating
source data, exact source-operator tail and signed coefficient
comparison. Its
[certificate](../certificates/source_norms/broad_clipped_identity.json)
stores the rational results and input hashes.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/broad_clipped_identity.py --check
```

The ordinary measure proof carries the arbitrary-family and
independent-residue quantifiers. The small-r branch is explicit;
the other branch continues to be handled by profile85's actual
mass-surplus bound, without silently imposing saturation.
