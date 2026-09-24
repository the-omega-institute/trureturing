# Complete-query comparison admits three more all-height old pair towers

Let P={3,5,7,11,13,17,19}. Consider any finite family of pairwise distinct
P-smooth numerical moduli greater than one, with globally fixed arbitrary
residues. Pure originals are unrestricted. Allow every mixed modulus of
the following forms, with every displayed exponent positive:

    3^a*q^b, q in {5,7,11,13,17,19};
    3^a*5^b*7^c;
    5^b*7^c, 5^b*11^c, 7^b*11^c, 7^b*13^c.

There is no bound on family size or exponent. The full actual survivor U
has Haar mass at least89827/2239488. Its ONE uniform law satisfies

    R_P(H(.|U))<=195749971/17965400
                =10.8959428122...<565/51.                 (CQ1)

Arbitrary additional distinct originals touching23 or29, and otherwise
supported on P, leave full Haar survivor at least

    167202479/275904921600>0.                              (CQ2)

The additional old pair towers extend
[report556](556-joint-root-queries-admit-the-old-five-seven-tower.md).
The new ingredient is an application of the existing complete-query
comparison to the same actual pure-product source and survivor. It
controls all numerical queries jointly, including queries whose phases
depend on their entire labels. This is an ordinary theorem application
with exact rational computation; no new Lean verification or resolution
of unrestricted Erdős #7 is claimed.

## 1. Condition the complete query on one actual survivor

For ANY finite distinct-modulus P-smooth family, let S_p be its complete
actual pure-p survivor. Define

    w_p=H_p(S_p)>=(p-2)/(p-1), a_p=1/w_p,
    rho0=product_p H_p(.|S_p), Omega=product_p w_p.

Let ell be the probability of the actual mixed union under rho0, and
suppose s=1-ell>0. Then

    rho=rho0(.|U)=H(.|U), H(U)=Omega*s.

For every prime p, positive exponent e and prefix r, the coordinate
probability under rho0 is at most a_p/p^e. This bound holds conditional
on every preceding coordinate history, since rho0 is a product law.

Choose a finite exponent box and, for every numerical label d in it,
choose a cylinder maximizing its probability under THIS rho. Include
the unit label. Their sum L is one legal finite complete query, and

    integral (L-1) d rho
       =sum_(d in the box,d>1) max_r rho([r]_d).

Every label has its own fixed phase. No consistency among those phases
is imposed beyond their being actual cylinders. For any integer tau>=0,
the pointwise bound L-1<=tau+(L-1-tau)_+ gives

    integral (L-1) d rho
       <=tau+(1/s)*integral (L-1-tau)_+ d rho0.           (CQ3)

Apply Michael Schroeder's existing
[conditional convex comparison](../../../../../Library/Arith/schroeder2026noncoverage.md#conditional-comparison-and-the-unrestricted-positive-part-bound),
source Proposition `prop:comparison`, with unit weights, the coordinate
caps above, and h(l)=(l-1-tau)_+. The proposition permits arbitrary
coordinate support and separately labelled phases. Its finite version
is also present as `Erdos7.ThreePrime.convex_load_comparison`; the
namespace does not impose a three-coordinate restriction. This
application does not change or rebuild that declaration. Earlier
applications to completed queries are
[report348, CP4](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md)
and [report19-1, PR6](../001-064/19-1-same-law-inputs-and-definitions.md#complete-test-comparison-inside-the-retained-pure-geometry).

Let the auxiliary K_p be independent nonnegative integers with

    Pr(K_p>=e)=a_p/p^e, e>=1, V=product_p(1+K_p).

The nested indicators in the comparison complete the exponent box into
this product. Thus CQ3 is at most tau+E(V-1-tau)_+/s. Its mean
EV=product_p(1+a_p/(p-1)) is finite. Increasing the finite boxes and
using the nonnegative query sums proves

    R_P(rho)<=tau+B_tau(a)/s,
    B_tau(a)=E(V-1-tau)_+.                               (CQ4)

Only finite maximizing phase choices were needed. No infinite maximizer
is assumed. Equivalently, monotone completion is justified by the finite
auxiliary mean. The chosen queries can be dependent under rho0; the
comparison theorem, rather than an independence assertion about them,
supplies the bound. Independence belongs to the auxiliary K_p and to
the prime coordinates of rho0, not to the conditioned law rho.

The tails of K_p increase with a_p. Coupling their inverse distribution
functions by one uniform variable per prime makes V and its hinge
nondecreasing in all a_p. Consequently the endpoint substitution

    a_p=(p-1)/(p-2)

is valid simultaneously. It does not optimize the actual source or the
actual survivor separately for different queries.

## 2. An exact complete-tail bound at tau=5

At these saturated caps, write N_p=1+K_p. Its full distribution and mean
are

    Pr(N_p=1)=1-a_p/p,
    Pr(N_p=n)=a_p*(p-1)/p^n, n>=2,
    EV=4096/935.

Use tau=5. For every positive integer v,

    (v-6)_+=v-6+(6-v)_+.

Therefore the exact infinite-tail hinge is determined by its full mean
and five low-product probabilities:

    B5=EV-6+5 Pr(V=1)+4 Pr(V=2)+3 Pr(V=3)
              +2 Pr(V=4)+Pr(V=5)
      =19132074022251234990036997833948759259
        /18473247078046657922374787501704265625
      <259/250.                                         (CQ5)

The low probabilities have finite computations. Products1,2,3,5 use,
respectively, all factors1 or exactly one factor2,3,5. Product4 also
includes two factors2, besides one factor4. A multiplicative convolution
produces the same probabilities. All larger values contribute through
the FULL mean in CQ5; the calculation discards no positive tail.

Hence for arbitrary mixed supports the following is a sufficient
conditional bridge:

    ell<=33/40
       => R_P(rho)<=5+(259/250)/(7/40)
                    =273/25<565/51.                     (CQ6)

Since Omega>=935/4096, the same premise gives

    H(U)>=1309/32768.

The unrounded CQ5 allows the strictly larger loss threshold

    ell<93156290569797077871456808548959521991
          /112288364592048312861493806382908281250
       =0.8296165939208445....                            (CQ7)

CQ6 is the simpler sufficient bound used here. It does not assert that
every P-smooth family meets its loss premise. Exact evaluation for
tau=0,...,10 makes tau=5 the unique best threshold in that checked range
for CQ7 and for the enlarged-support loss below. No global optimization
over arbitrary representations is claimed.

## 3. Apply the larger loss allowance to three old pair towers

Report556 JQ11 proves, uniformly in the complete actual pure source,
that stars, the357 triangle tower and the entire old5/7 tower have mixed
union mass at most

    ell_base=1527182/2044845.

Use the complete pure source of the WHOLE enlarged family. Its extra
mixed originals can be charged under that same source. The complete
old p/q pair tower has total cap

    sum_(b,c>=1) a_p*a_q/(p^b*q^c)
       <=1/((p-2)*(q-2)).

Thus adding every old5/11, old7/11 and old7/13 numerical label costs at
most1/27+1/45+1/55. These towers have distinct supports from the base
and each other. Every finite original is charged once, at its own full
numerical label, with no phase restriction. The full actual mixed loss
is bounded by

    ell<=1527182/2044845+1/27+1/45+1/55
        =1685537/2044845<33/40,
    33/40-1685537/2044845=11681/16358760>0.              (CQ8)

Applying CQ4--CQ5 with this exact survivor lower bound, while using the
rounded numerator259/250, gives CQ1 and

    H(U)>=935/4096*(1-1685537/2044845)
         =89827/2239488.

More generally, any additional mixed numerical inventory beyond the
report556 base whose saturated cap sum is at most

    sum_(extra d) d^(-1)*product_(p|d)(p-1)/(p-2)
       <=1278521/16358760                              (CQ9)

fits CQ6. This is a condition on the inventory, not a new restriction
on how its arbitrary fixed residues may be selected.

## 4. The same-law23/29 extension

Tensor the appropriate ONE final law rho with independent Haar
coordinates at23 and29. A new numerical label is uniquely d*23^j*29^k,
where d is P-smooth, j,k>=0 and j+k>0. The unit d is included. Distinct
original labels and their fixed residues therefore give total extra
loss at most

    (1+R_P(rho))*sum_(j+k>0)23^(-j)*29^(-k)
       =(1+R_P(rho))*51/616.

For CQ1, subtract this bound from one and multiply by89827/2239488.
The result is exactly CQ2. Under only the uniform premise CQ6, the
relative reserve is at least101/7700 and the extended Haar mass is at
least1717/3276800. All phases and all finite heights at23 and29 remain
arbitrary, including arbitrary P-smooth cofactors.

The original query bound is not asserted again after conditioning on
these additional survivors. No further fresh-prime continuation or
membership in the separate entropy/unused-label class G is inferred.

## 5. Reproduction and remaining obligation

The [standalone exact calculation](../../frontier/cover-geometry/complete_query_conditioning.py)
uses only the Python standard library and retains
[rational result data](../../frontier/cover-geometry/complete_query_conditioning.json).
Its multiplicative convolution keeps products through10, allowing exact
hinges at all eleven tested thresholds. CQ5 uses only products through5.
The earlier all-height loss theorem is an explicit cited input; this
program does not rerun or independently establish report556's optimizer.

All27 checks pass. The result JSON SHA256 is
`23f4488f22a3bc35434a408d07203c2c0813a2faeb24c420fdc281af158e8a42`.
A separate calculation enumerates the267 factor assignments with product
at most10 and independently evaluates the closed forms at1,...,5; it
reproduces the exact hinges and all displayed endpoint constants.
Running a copied script at a path containing spaces from a different
working directory gives identical JSON bytes on the tested macOS host.
Other operating systems were not tested.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/complete_query_conditioning.py
```

The program accepts `--output`. The general domination in CQ4 uses the
cited comparison theorem and the argument in Section1; finite numerical
checks alone do not prove that domination. No Lean was added or built.

What remains is a uniform actual-loss estimate, or a stronger coupled
survivor/query argument, for unrestricted mixed supports. CQ6 is valid
for those supports conditionally; CQ8 establishes its premise only for
the specified enlarged family. Neither the full3-divisible mixed family
nor arbitrary P-only mixed supports are settled here. Unrestricted
Erdős #7 remains open.
