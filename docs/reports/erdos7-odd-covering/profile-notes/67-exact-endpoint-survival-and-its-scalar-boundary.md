[Index](../marked_head_profile.md) · [Allocated survival](53-allocated-seven-thresholds-sharpen-actual-survival.md) · [Physical comparison](56-exact-survival-limits-the-fixed-numerator-comparison.md) · [Endpoint numerator](65-endpoint-numerator-from-common-cost-constraints.md)

# Exact endpoint survival and the boundary of the fixed scalar constraints

For the actual endpoint class of profiles59,64 and65, the physical
AP11/T4, AP13/T5 survival comparison has the uniform raw denominator
lower bound

    d_exact=4067559874193/52947452250000
           =0.07682257977187183... .                    (SC1)

Here the source tends to theta404, S=D=3/20, and the forbidden carrier
mixture tends to(root0,cell1). Every original survival test retains
its independently chosen residues. The statement is a limiting endpoint
comparison, not an assertion that a finite original family attains that
source or that the same bound holds on the entire source domain.

This improves profile53's denominator at the endpoint:

    d53=40593580507/534822750000
       =0.07590099805402818...,
    d_exact-d53=3485386/3781960875>0.                   (SC2)

There is also an exact obstruction to obtaining a larger bound from
the currently retained scalar information. Fix all54 constraints of
profile65 and add profile53's three survival hinge bounds. Among
abstract positive-integer load laws satisfying these57 constraints,
(SC1) is the optimal guarantee for the exact AP11 survival expression.
Two finite rational load laws attain the bound in this relaxation.
They are not claimed to come from actual congruence families.

Keeping profile65's numerator upper bound N65 unchanged, the ratio
comparison for403 requires

    d>=N65/(403-C0)=0.09439030471077034... .             (SC3)

The gap from(SC1) is0.0175677249388985... . This is an obstruction
to that fixed scalar comparison, not an obstruction to stronger
original-family geometry, a smaller numerator, a different physical
comparison, or a joint numerator-denominator estimate. There is no
global K update and no claim to resolve unrestricted Erdős #7. The
proof and certificates here are ordinary mathematics and exact rational
verification, not Lean verification.

## 1. The scalar constraints apply separately to every original test

Let mu be the raw surviving endpoint measure, of mass D=3/20. For
every complete independently labelled original357 test A, profile65
gives all54 bounds: first moment, second moment,46 transformed costs,
and six raw81 costs. In particular,

    integral A dmu<=L=1157/1800,
    integral A^2 dmu<=Q=469/100.                       (SC4)

Profile53 supplies three further bounds for h_t(v)=(v-t)_+:

    integral h_(5/2)(A) dmu<=81281/220500,
    integral h_4(A) dmu<=U4=2701424/12403125,
    integral h_5(A) dmu<=U5=2028798479/12155062500.     (SC5)

These are uniform bounds for each original test, so all57 inequalities
may be used on any one of the tests appearing in the physical survival
comparison. This does not identify different original tests or assert
that their maxima have a common actual residue layout.

To reconstruct(SC5), the old profile46 endpoint margins are

    m25=68963/441000,
    m4_old=-23627747/347287500,
    m5_old=-216990479/12155062500.

Profile53 adds2/8575 to m4 and1131/1200500 to m5, retaining m25.
With barriers7/2,1,1, the three raw upper bounds are
(7/2)D-m25,D-m4,D-m5. Their weighted survival denominator is exactly
the endpoint controller d53 in(SC2).

## 2. A moment-hinge interpolation gives a useful exact improvement

For1<=t<=4 and every real v>=1, convexity in the threshold gives

    h_t(v)<=(4-t)*(v-1)/3+(t-1)*h_4(v)/3.             (SC6)

Equivalently, verify it on v<=t, t<=v<=4 and v>=4. Integrating gives
the uniform bounds

    U(t)=(4-t)*(L-D)/3+(t-1)*U4/3, 1<=t<=4.          (SC7)

In particular,

    U(5/2)=70507267/198450000,
    U(5/3)=385493909/893025000,
    U(5/4)=559466017/1190700000,
    U(1)=887/1800.                                   (SC8)

Keep U(4)=U4 and U(5)=U5. Substituting into the original three-hinge
physical expression gives

    d_three=(919/924)D-U(5/2)/22-U4/6-4*U5/33
           =(235/231)D-L/44-25*U4/132-4*U5/33
           =27278447033/356548500000
           =0.07650697459952853... .                  (SC9)

This already improves d53 by2645633/4365900000. It uses the uniform
first moment and h4 bound on the same test. It does not add separate
deletion credits to costs whose deletion has already been included.

## 3. The full AP11 count law supplies the best retained denominator

Use the uncompressed physical survival expression from profile56:

    d>=D-U4/6-(1/7)*sum_(n>=1)p_n*n*U(5/n),          (SC10)
    p1=28/33, p_n=50/(3*11^n) for n>=2.

Every U(5/n) must be valid for each independent original test in its
own AP11 block. The count law is an auxiliary comparison law; no
independence of actual forbidden events is imposed.

For n=2,3,4 use(SC7), and for n=1 use U5. For every n>=5 and every
integer v>=1,

    n*h_(5/n)(v)=n*v-5.

Consequently the entire infinite remainder is bounded by

    T1*L-5*T0*D,
    T0=sum_(n>=5)p_n=(50/3)*r^5/(1-r),
    T1=sum_(n>=5)n*p_n=(50/3)*r^5*(5-4r)/(1-r)^2,
    r=1/11.                                         (SC11)

No exponent or count cutoff is substituted for these complete tails.
Combining(SC7),(SC10),(SC11) gives the independent coefficient form

    d_exact=(945008/922383)*D
             -(45253/1844766)*L
             -(346061/1844766)*U4-(4/33)*U5,          (SC12)

which is(SC1). On the endpoint mass D this gives the normalized bound

    rho_endpoint>=4067559874193/7942117837500.

The endpoint passage uses the moment limsup bounds of profiles59,64
and65. All finitely many required hinge integrals have at most linear
growth; the complete count tail in(SC11) is controlled by the same
uniform first moment. Thus the physical comparison passes to liminf
without a common maximizing layout or an interchange of an uncontrolled
infinite sum and limit.

## 4. Two small abstract laws prove exact scalar optimality

Define raw load laws W and V, each of mass D, by

| Load | W mass | V mass |
| --- | ---: | ---: |
| 1 | 17366767/297675000 | 5264239021/48620250000 |
| 4 | 5673091/297675000 | 0 |
| 7 | 2701424/37209375 | 0 |
| 9 | 0 | 2028798479/48620250000 |

Both laws satisfy all57 scalar inequalities. The accompanying checker
evaluates every cost using the pinned original cost formulas and records
all114 rational slacks; every slack is nonnegative. This is finite
support feasibility, with no atom at infinity or escaped second moment.

The law W has

    integral v dW=L, integral h_4(v) dW=U4,
    integral v^2 dW=129677159/33075000
                   =3.9207001965230535...<Q.           (SC13)

Its support is contained in{1} union[4,infinity), precisely where(SC6)
is equality for every1<=t<=4. Thus W attains all the bounds U(t) used
above and also all the affine n>=5 tail bounds. The law V attains U5.
Together these give feasible primal values equal to the all-load dual
bounds for each survival target.

The laws can coexist on one abstract measure space: give a pair(i,j)
mass W(i)*V(j)/D, and let its two load coordinates be i and j. The
coordinate marginals are exactly W and V. Assign W to the h4 test and
every n>=2 AP11 test, and V to the n=1 AP11 test. Every separately
labelled scalar test then satisfies all57 constraints on the same
mass-D space, while(SC9) and(SC10) are equalities.

It follows that no consequence of just these57 separate scalar
constraints can improve d_three for the three-hinge expression or
d_exact for the exact AP11 expression. This does not construct original
residue classes. Actual geometric restrictions can exclude W or V,
or constrain different tests jointly; those restrictions are precisely
the information absent from the relaxation.

## 5. Exact reproduction

The [checker](../frontier/endpoint_survival_scalar_barrier.py) pins the
profile65 numerator and all54 of its original bounds, reconstructs the
three profile53 endpoint bounds, verifies the two finite rational laws,
and checks six all-integer majorants by exact affine tails. It evaluates
the full AP11 expression in both cost and coefficient forms and verifies
that the product-law primal attains it. The
[certificate](../certificates/source_norms/endpoint_survival_scalar_barrier.json)
retains the rational data and strict remaining gap to(SC3).

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/endpoint_survival_scalar_barrier.py --check
```

The program uses only the Python standard library and pinned repository
cost routines. Assertions are not used for checks. Default execution
does not write; only `--output PATH` writes through the existing
certificate writer. A later change of the numerator or scalar caps
defines a new relaxation and does not alter the fixed65 statement here.
