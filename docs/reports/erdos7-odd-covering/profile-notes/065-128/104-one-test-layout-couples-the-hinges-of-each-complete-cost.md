[Index](../../marked_head_profile.md) · [Complete stop-loss generator](98-a-complete-stop-loss-profile-strengthens-the-whole-face-comparison.md) · [Complete AP11 denominator](101-neighboring-hinges-strengthen-complete-ap11-survival.md)

# One test layout couples the hinges of each complete cost

The hinges in the expansion of one original AP cost are functions of the
same original357 test. Combining their source objectives before taking
the head and cylinder maxima improves11 of the current linear-cost upper
bounds. On both complete actual saturated K-control beta faces,

    N<=35.185034731037741176534799109826...,
    d>=1358432973299/17084377926000,
    C0+N/d<=464.0998998398563471248814419042... .       (CL1)

The numerator decrease from101 is exactly

    49781836352241400652355581/457409841096473698416984000
    =0.108834204862990174264639866964... .            (CL2)

The complete face comparison decreases by1.36875703380454740659....
Its denominator is101's unchanged complete AP11 expression. All52 costs,
the negative mass term, complete square complements and original tails
remain present. One legal substitution in the existing52 all-load
majorants gives zero additional improvement for these new bounds.

The scope remains r=rho=0 and mass D=53/360 on both entire actual control
faces. This is an ordinary exact-arithmetic proof, with no off-face
extension, new global K, scalar optimality, Lean or unrestricted Erdős7
claim. The comparison remains above403.

## 1. The same cost has one original test

For a fixed original AP cost f and its original complete357 test A,
retain98's exact expansion for every positive integer load:

    f(v)=f(1)+d1*(v-1)+sum_(t=2..8)kappa_t*h_t(v),
    d1>=0, kappa_t>=0, h_t(v)=(v-t)_+.               (CL3)

The affine continuation is exact, so(CL3) includes the entire cost tail.
Keep the established affine contribution f(1)*D+d1*U1, where U1=L-D.
The improvement below concerns the remaining curvature sum. Different
cost indices may still have independently chosen original tests; no
layout is identified across two different f's.

Use98's six-label head B, original selected labels

    (M1,M2,M3,M4)=(25,27,75,81),

and k_t=min(t-1,4). Its threshold bridge is

    f_t(v)=w*h_t(v)+g_(t,m)(v),
    m=1_(ROOT(c)=T)+1_(s=F),
    g_(t,m)(v)=1/[5*7^max((t-v)_+-m,0)]
                         +(6/35)*max(m-(t-v)_+,0).

All thresholds in(CL3) use the same B layout, the same original21/35
projections T,F, and the same original selected test cylinders M_i,
because they are evaluated on the same A. The source density w, source
LP U_L and arbitrary-cylinder operators P_(M_i) are exactly those of98.

## 2. Combine the head and each selected label before its maximum

Define the nonnegative combined head objective

    H_f(v)=sum_(t=2..8)kappa_t*f_t(v),               (CL4)

and for each selected original label M_i define its single retained
rectangle objective

    Z_(f,i)(B)=sum_(t:k_t>=i)kappa_t*
                               [f_t(B+i)-f_t(B+i-1)]. (CL5)

Every summand is nonnegative by98's integer-convex bridge argument.
Multiply98's pointwise threshold inequalities by kappa_t and add them
before integrating the head and retained selected-label terms. Linearity
then gives, for this one fixed original layout,

    integral sum_t kappa_t*h_t(A)
      <=sum_t kappa_t*(Zplus+R_(k_t))
                       +U_L(H_f(B))+sum_i P_(M_i)(Z_(f,i)(B)), (CL6)

where

    Zplus=779/12600,
    R_k=163/1800-sum_(i=1..k)c_i,
    (c1,c2,c3,c4)=(2/125,7/270,4/375,7/810).

The old and positive-seven remainders are complete. For a threshold
whose prefix omits M_i, that threshold's contribution remains among its
peeled cap R_(k_t). For a threshold whose prefix retains M_i, its
contribution is in(CL5). Thus the retained and peeled contributions
partition the curvature weights for each label; none is silently lost
or charged twice. Each retained M_i is bounded by one P operator after
all its relevant threshold coefficients have been added.

Taking one maximum over the common B,T,F in(CL6) supplies the new cost
upper bound

    B_f^joint=f(1)*D+d1*U1+sum_t kappa_t*(Zplus+R_(k_t))
       +max_(layout,T,F)[U_L(H_f(B))+sum_i P_(M_i)(Z_(f,i)(B))]. (CL7)

The mean contribution d1*U1 is retained separately as stated. No claim
is made that this is the strongest possible use of the mean observation.

All operators in(CL7) are positive homogeneous and subadditive, being
maxima of nonnegative linear functionals. Consequently(CL7) is no worse
than multiplying98's separate threshold maxima by kappa_t and adding
them. A strict gain is possible when different threshold maxima require
incompatible original layouts or maximizing source/cylinder choices.
This is an inequality between source bounds, not a construction of a
source attaining their maxima.

## 3. The exact inventory avoids calculations with no possible gain

Among the41 linear costs,27 have only kappa_2 nonzero and one is affine.
For a single nonzero curvature, positive homogeneity makes(CL7) exactly
the previous one-hinge formula. The affine cost is unchanged. Repeating
those28 enumerations cannot improve the current bounds within(CL7).

There are13 costs with several nonzero curvatures. For R17(0,0) and
R19(0,0), a concrete original head/projection choice already gives a
lower bound on the maximum in(CL7) above the current vector cost bounds:

| Cost | Existing upper bound | Fixed-layout lower bound on(CL7) |
| --- | ---: | ---: |
| R17(0,0) | 5.92895325764... | 6.86197568107... |
| R19(0,0) | 4.73610675081... | 5.48546864119... |

The certificate stores the exact layouts, rational values and matching
LP primal/dual data. Since the full maximum is at least this fixed value,
the proposed fixed generator cannot improve these two current bounds.
This excludes only(CL7) with its stated observations and prefix order;
it is not an actual-family counterexample or a bound on other methods.

The remaining11 costs have original inventory indices

    1,2,7,10,17,18,23,26,32,33,36.

For each, the program factors its rational curvature vector into a
positive rational scalar and a primitive nonnegative integer vector.
It precomputes the combined head and retained-increment arrays, then
checks all12500 original head layouts and all10 positive-seven projection
choices. Every one of the1375000 LP evaluations has a feasible primal
and dual with equal values; every selected cylinder bound is exact in
the same integer scaling. Each of the11 resulting cost bounds is
strictly smaller than its current upper bound.

For example R19(1,0) decreases from1.4372128654013683... to
1.4214633614446048..., and R5(0,0) decreases from0.2035144462778034...
to0.2015553695100828.... Some two-threshold costs have a new maximizing
common head/projection that differs from every individual-threshold
controller considered initially; evaluating only those old controllers
would not certify the new maximum.

## 4. The complete face scope and signed consumer remain intact

The source LP keeps the whole root1 beta mass in one group constraint,
as in83 and98. Formulas(CL4),(CL5) only combine nonnegative objectives
on that same feasible set. They do not fix a particular beta distribution
or interpolate separately optimized vertex values. The existing first-
beta cell permutations and root0-cell exchange preserve all summed
objectives and transport(CL7) to both complete actual faces.

For infinite original label families,98 already pays all peeled tails
by complete geometric sums. The curvature sum is finite and nonnegative;
its combination with these valid bounds therefore preserves the full
tail argument. Original residues remain arbitrary, and selected labels
retain their identities throughout every threshold term.

The complete consumer takes the minimum of the new cost bound and the
corresponding current bound, independently for each cost. It retains all
other costs, and performs one simultaneous legal substitution into the
52 existing all-load majorants. That substitution supplies no further
gain here. The final numerator is still

    N=r_mass*D+sum_(i=1..52)w_i*cost_i+c_square*(374/75),
    r_mass<0, w_i>0, c_square>0.                     (CL8)

Its exact value is

    8900862274618738486076077484437084354260312604177
    /252972956902243138190838916958250000000000000000.

The positive denominator remains101's
1358432973299/17084377926000, with its original AP11 count probabilities
and complete affine tail. The same offset C0=185694867601/8599322160
then gives the exact comparison bound

    45863942113753007251795118139309083557904353324321601
    /98823426011466392651464381291661827125000000000000,

which is(CL1). The lower-dimensional saturated-face scope is unchanged.

## Reproduction

[whole_cost_common_stop_loss.py](../../frontier/comparison-bounds/whole_cost_common_stop_loss.py)
checks the existing complete cost expansions, same-test combined
objectives, all1375000 required joint layouts and the complete signed
consumer. The[certificate](../../certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json)
retains the precise no-gain dispositions, fixed-layout obstructions,
new maximizing witnesses, exact curvature scalings,52 cost bounds and
101's unchanged complete denominator.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/whole_cost_common_stop_loss.py --check
```
