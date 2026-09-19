[Index](../../marked_head_profile.md) · [Joint135/125 bridge](225-two-original-tests-share-the-complete-retained-bridge.md) · [Preceding survival bounds](224-the-retained135-test-strengthens-two-complete-survival-bounds.md) · [Exact cost identities](202-eight-original-costs-have-an-exact-load-two-remainder.md)

# The joint135/125 records strengthen two complete survival bounds

On both complete actual saturated K faces, with r=rho=0, the full
comparison is

    K <= 1525429429089836694161505919795127725092279951226687/3811013517527643475906837007488553854129829700240
       =400.268700720705821001295395089615... .                              (JS0)

The complete comparison improves225 by2.131869513920535517926025704951... .
The two new uniform bounds are

    U4 =1261295471736052561/6945750000000000000
       =0.181592408557182818414138142029...,

    V0 =37360014652555708409071/228808632937500000000000
       =0.163280616526216241770735613418... .            (JS1)

U4 bounds the independent AP13 hinge. V0 bounds the first original
AP11 block function, including its full count-tail coefficient.
Each bound covers all62,500,000 containing head/seven-projection
choices. AP11 blocks1,2,3 are inherited unchanged from224/218.
The uniform U4 also strengthens original numerator cost41 through
202's exact identity. The complete numerator retains all52 costs,
the negative actual-mass term and the complete square.

These are ordinary source inequalities with exact rational dual
certificates. They do not prove actual-family attainment, an
off-face or global comparison, Lean verification or an unrestricted
Erdos7 resolution.

## 1. Four joint states of the same raw and surviving source

Use225's joint135/125 model without changing any constraint. In
each old source rectangle and selected25/27/75/81 mask, the same
raw source x and actual survivor y are partitioned into four states:

    neither, 135-only, 125-only, both.

The three marked states have raw and surviving variables. Their
complement is obtained by subtraction from x and y; both marked
and complement masses are nonnegative and satisfy the same
face survivor domination. The135 test retains an independent
25-coordinate profile, and the125 test an independent five-slot
profile. The two original labels are not identified with any old
selected test. Their surviving caps are1/135 and2/625, and the
raw intersection cap is1/3375.

For each nonnegative hinge coefficient vector a, let H_a(v) be its
survivor hinge combination and G_a(v) its complete two-depth seven
increment. The old selected load uses all four mask indicators at
thresholds t>=2 and the empty selected set at t=1. Retaining135 and
125 adds respectively1,1,2 on the three exclusive marked states.
Thus the joint-state addition to the old x/y objective is

    sum_(j in {135-only,125-only,both})
        [Delta_(k_j)G_a(v)*x_j+Delta_(k_j)H_a(v)*y_j],
    (k_135-only,k_125-only,k_both)=(1,1,2).             (JS2)

Each increment in(JS2) is evaluated separately within its threshold
term, and is zero at t=1. The raw coefficient is only the change
in G_a; the survivor hinge change is charged to y_j. In particular
the joint state uses a two-unit difference, not a sum of two
one-unit differences at the same old load.

The complete zero-seven remainder at t>=2 is

    R6=19/648-1/135-2/625=7579/405000.                 (JS3)

At t=1 the original empty-selection remainder is R0=163/1800;
the remaining positive-seven constant is Z=2669/88200. Every
exponent tail is included. The original two-, four- and
six-projection pruning bounds remain separately valid alternatives
with their own complete tails and whole-hinge deletion credits;
no old deletion credit is additionally subtracted from(JS2).

Both nested and disjoint27/81 geometries are checked. Each branch
has3705 variables,7163 inequalities and56 equalities. The branch
maximum gives a containing bound for every actual configuration;
it does not assert that a maximizing LP point is realizable.

## 2. Two survival gains in the complete denominator

The AP11-block0 coefficient vector is unchanged:

    a1=1355/263538, a2=20425/263538,
    a3=25/363, a5=28/33.                              (JS4)

It uses one original head and one independent seven-projection
tuple throughout. The omitted count probability and first moment
remain tau0=5/43923 and tau1=17/29282. Their complete denominator
tail is

    T=(tau1-4*tau0)*(L-D)+(tau1-5*tau0)*D
     =3337/52707600,
    D=53/360, L=1151/1800.                            (JS5)

The full positive denominator, using the three inherited block
bounds V1,V2,V3, becomes

    d=D-U4/6-(V0+V1+V2+V3+T)/7
     =81853795843929536915591/949132107000000000000000
     =0.086240677393847279170791974904... .             (JS6)

Its increase over225 is exactly

    (U4_old-U4)/6+(V0_old-V0)/7
     =70512711358645860859/152539088625000000000000
     =0.000462259949198944945899108881... .             (JS7)

The two uniform estimates apply to their independent original
labels. A common maximizing family is neither needed nor asserted.

## 3. The same hinge estimate lowers one original numerator cost

All eight202 exact positive-integer identities are checked again,
including their entire polynomial tails. For cost41 the identity is

    f41(n)=a*(n^2-1)+b*(n^2-9)_++c*h4(n)
           +e*(n-5)_+*(n-4)/2-r*1_(n=2),

    a=312522845/736900164, b=127212451/736900164,
    c=948/143, e=632/429, r=636062255/736900164.        (JS8)

Discarding its nonnegative load-two charge gives the valid bound

    integral_mu f41<=a*(Q-D)+b*U9+c*U4+e*T5,
    Q=8201/1800, U9=17859883/4630500, T5=2303/2700.

No positive load-two mass is assumed. Comparing all eight identity
bounds with225's costs improves only cost41, to

    532742519052963522956587553/106631756543812500000000000
     =4.996096250501810461890656205578... .             (JS9)

All other51 cost entries retain their225 values. With the original
52 weights, signed actual-mass coefficient and complete square,
the numerator is

    N=73434455197278081200470750848458681382270438899/2248648505797716783918568150740000000000000000
     =32.657151621492271971173583938528...,

and its decrease from225 is exactly

    1864666415737488778231/238378140000000000000000
     =0.007822304577665925148300091610... .             (JS10)

Substitution of N and d into the unchanged original offset plus
N/d proves(JS0). Neither the numerator feedback nor the denominator
gains are counted twice.

## 4. Complete rational scans and consumer

The [helper](../../frontier/transport/retained135125_survival_comparison.py)
uses225's model, complete scan and exact column checker. The
[proposal program](../../frontier/transport/propose_retained135125_survival_duals.py)
can suggest prices, but every repaired rational dual must cover
all3705 objective columns. The
[certificate](../../certificates/source_norms/retained-transport/retained135125_survival_comparison.json)
contains2792 distinct branch duals, or10,344,360 checked columns.

| Test | Two-projection visits | Four-projection visits | Six-projection visits | Joint two-branch uses | Distinct branch duals | Exact source-capacity LPs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| AP13 | 125000 | 5050 | 2260 | 1162 | 2322 | 132313 |
| AP11 block0 | 125000 | 2550 | 590 | 236 | 470 | 128143 |

Each row covers all62,500,000 original choices through explicit
evaluation or a complete certified alternative. Neither scan uses
prefix pruning. Both maximizing containing layouts are
(1,4,2,1,2,4,2), with seven-projection tuple(1,4,4,1,4,1,4).
These are witnesses to the containing optimization only.

The checker reconstructs the source pins, both scans, every count
term, the eight identities and the entire52-cost comparison:

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/transport/retained135125_survival_comparison.py --check
```

Numerical proposal software is not needed by this check. The final
comparison is confined to the stated saturated faces; transporting
all constraints, objectives and tails off those faces is a
separate obligation.
