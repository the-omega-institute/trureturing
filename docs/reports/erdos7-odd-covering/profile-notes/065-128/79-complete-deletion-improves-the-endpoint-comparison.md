[Index](../../marked_head_profile.md) · [Previous uniform comparison](70-a-complete-endpoint-ratio-with-uniform-survival.md) · [Complete pure3 deletion](77-complete-pure3-deletion-gives-a-uniform-linear-gap.md)

# Complete deletion improves the endpoint numerator and survival together

At the actual source404 endpoint, S=D=3/20 and carrier(0,1), the
additional complete pure3 deletion of profile77 improves the full
AP comparison to

    N <=35.767543767138505...,
    d >=0.07689072000091865...,
    C0+N/d <=486.7678681333996... .                    (CD1)

This lowers profile70's endpoint comparison by0.5742452035322124... .
Every original test still chooses its own residues; the bounds use
one actual source and all original exponent tails. This is a uniform
endpoint and approaching-sequence comparison, not a new global K
bound or a solution of unrestricted Erdos #7. The sufficient threshold
403 is still not reached. No Lean verification is claimed.

The old scalar witness W is excluded by the stronger mean bound.
Nevertheless, a modified abstract witness shows that the revised
scalar survival bound is again sharp for precisely the retained
constraints. That distinguishes a proved geometric gain from a claim
that scalar optimization alone can now remove the remaining gap.

## 1. A new mean bound on the same actual endpoint

Profile77 gives, for every complete original357 test A,

    integral A dmu <=L=16/25,
    Lold-L=1157/1800-16/25=1/360.                    (CD2)

The surviving mass remains D=3/20. Retain profile69's independent
second-moment bound Q=114/25 and all52 old transformed/raw cost
constraints from profile65. These statements are uniform in the test,
so they may be applied to each independently labelled numerator or
survival test. No equality of those tests is required.

The extra deletion in(CD2) is already incorporated in the new mean.
It is not deducted again from the old cost caps or the physical
denominator. Those improve only by applying valid all-load inequalities
to the strengthened mean constraint.

## 2. Reuse the complete all-load cost majorants

Index the54 scalar costs as in profile65: mean, square,46 transformed
AP costs and six low raw81 costs. Every retained rational majorant is
an inequality for all positive integer loads v:

    f_i(v)<=alpha_i+sum_j w_ij*f_j(v), w_ij>=0.

For the revised bounds b0=L, b1=Q and all other old b_j, integration
therefore gives

    integral f_i(A) dmu
      <=min(b_i,alpha_i*D+sum_j w_ij*b_j).             (CD3)

All52 majorants and their old min branches are retained. The checker
verifies each inequality on its finite polynomial pieces and complete
tail through the existing all-load verifier. It does not infer the
infinite-domain inequalities from an arbitrary finite load cutoff.

Thirty-seven of the52 cost bounds improve relative to profile70.
The complete positive-weight expansion of the numerator is

    N =r*D+sum_i beta_i*cost_i+c_square*Q,             (CD4)

with the same r, beta_i and c_square as profile70. All beta_i are
positive; r is negative and is retained. Since D is fixed at the
endpoint, that signed term causes no ambiguity in the comparison.
The transformed-square complement and the complete raw81 square tail
are included in c_square. Thus the exact new value is

    N=60321475386022830087519437143027730327824815714779
      /1686486379348287587938926113055000000000000000000.

The same value is obtained by subtracting the52 weighted cost gains
from the old complete numerator. This preserves all signed barriers
and every auxiliary-count tail; it changes no physical test law.

## 3. The complete AP11 denominator improves at the same time

Keep the uniform native hinge bounds from profile53:

    U4=2701424/12403125,
    U5=2028798479/12155062500.

For1<=t<=4, the pointwise hinge interpolation from profile67 gives

    U(t)=(4-t)*(L-D)/3+(t-1)*U4/3.                   (CD5)

For t<=1, use U(t)=L-t*D. With the complete AP11 count law

    p1=28/33, pn=50/(3*11^n) for n>=2,

the same physical comparison is

    d>=D-U4/6-(1/7)*sum_(n>=1)pn*n*U(5/n).          (CD6)

For n=1 use U5; for n=2,3,4 use(CD5). For every n>=5 the load
is at least1, so n*h_(5/n)(v)=n*v-5 exactly. The entire remainder
is T1*L-5*T0*D, where, with r11=1/11,

    T0=(50/3)*r11^5/(1-r11),
    T1=(50/3)*r11^5*(5-4*r11)/(1-r11)^2.

Consequently

    d=(945008/922383)*D-(45253/1844766)*L
                         -(346061/1844766)*U4-(4/33)*U5
     =30788205925733/400415107640625.                 (CD7)

The improvement over profile67's uniform denominator is exactly
45253/664115760. This is a uniform actual denominator, not the value
of one tensor witness. Combining(CD4) and(CD7), with the unchanged
comparison offset C0, gives(CD1). Each numerator coefficient is
nonnegative after retaining the fixed signed mass term, and d>0,
so the quotient direction is valid.

## 4. The revised scalar obstruction remains exact

Let W and V be profile67's two raw mass-D laws. W is supported on
{1,4,7} and has mean Lold and h4 integral U4. Define a new law W'
by transferring mass

    (Lold-L)/3=1/1080

from load4 to load1. Its masses stay positive, its total mass stays
D, its mean becomes L, and its h4 integral remains U4. Its support
still lies in the equality set {1} union[4,infinity) for(CD5).

All original scalar cost functions are increasing, so this transfer
cannot increase their integrals. The checker also verifies all57
revised inequalities directly, including Q=114/25. V already has
mean5880856333/12155062500<L; it remains feasible and retains h5
integral U5. The114 feasibility checks cover both laws against all
retained constraints, not only their first two moments.

Assign W' to the h4 test and all n>=2 AP11 tests, and V to the n=1
test. A product coupling of these raw laws on one mass-D space gives
these marginals simultaneously. W' attains every interpolation in
(CD5) and the complete affine tail, while V attains U5. Therefore
(CD7) is the exact best guarantee from these57 separate scalar
constraints for(CD6).

This constructs abstract load laws only. It does not realize W' or
V by actual congruence families. Additional common-source geometry
can still exclude them or strengthen the numerator. The result
does not claim that the full actual endpoint comparison in(CD1)
is attained or optimal.

## 5. Reproduction and endpoint passage

The [checker](../../frontier/endpoint-bounds/endpoint_complete_deletion_ratio.py) consumes
the pinned geometry and all-load comparison inputs. The
[certificate](../../certificates/source_norms/endpoint-bounds/endpoint_complete_deletion_ratio.json)
retains all52 majorants, each changed cost, the complete AP11 tail,
both revised scalar laws and all feasibility slacks.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint-bounds/endpoint_complete_deletion_ratio.py --check
```

For approaching finite families, use profile77's uniform mean limit,
profile69's square limit and the existing complete cost bounds. The
finite coefficient sums pass to limsup. The AP11 tail in(CD6) is
affine and controlled by the same complete first moment, as in
profile67. Thus the comparison retains arbitrary finite exponent
heights without silently replacing them by an infinite realization.
