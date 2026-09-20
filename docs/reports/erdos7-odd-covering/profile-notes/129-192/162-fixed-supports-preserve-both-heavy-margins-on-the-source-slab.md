[Index](../../marked_head_profile.md) · [Original vector theorem](../065-128/91-cell-vector-markers-retain-the-selected-deep-deletion.md) · [Jensen obstruction](159-the-optimized-heavy-margin-fails-late-factor-jensen.md) · [Complete comparison](157-a-signed-tail-comparison-covers-the-one-over-twenty-seven-neighborhood.md)

# Fixed supports preserve both heavy margins on the source slab

The complete original52-cost comparison on

    qK>=26/27, 0<=rho<=1/20000

improves from160's482.0442111467803... to473.11203393433925....
The new input is a uniform theorem for the two heavy terms on a
larger source slab; the other50 costs and complete denominator are
reused at exactly their previously certified domain.

Both original heavy costs retain their positive canonical margin
throughout the broad actual source slab

    Delta=z-3/4+(1/4-alpha1)+(1/4-sum_(j>=2)beta_j)<=1/18,
    z<=4/5, first_beta=2, 0<=r<1/2500.             (FS1)

For the same actual survivor mass S and residual rho as91, there
are complete bounds

    Cost_i<=C_i*S-m_i+P_i*rho, i=0,16,            (FS2)

with the original barriers C_i and

    m0=1193878489939499612/259995953549870913375
       =0.004591911811083232...,
    m16=1088704788427803234124/300295326350100904948125
        =0.0036254469946646155...,
    P0=1561488125/68994926=22.631926947787434...,
    P16=4549266250/254026773=17.908609381106455... . (FS3)

The source deficit and late factors are unrestricted within their
original simplices. This is a source-slab theorem, not an additional
concentrated-K radius. The actual first-beta condition is retained;
it is expressed below as a joint source-polytope constraint.
In particular rho<=1/100000 implies r<=5rho<1/2500, so the result
applies at that existing residual radius without another assumption
on r. The usual root1 relabeling selects first_beta=2.

The proof replaces adaptive capacity choices by fixed feasible
supports. The resulting absolute margins have the needed
concavity, and their exact minima over a new6x36x6 source product
and all18 carriers are precisely m0,m16. Every original heavy test
keeps all100 independent branches and its complete infinite tails.

This supplies replacements for indices0 and16 in the complete52
comparison. The local consumer is completed in section6. A complete
numerator/denominator target on the entire larger slab remains open;
neither result is a new global K or an unrestricted Erdos7 resolution.

## 1. Fix the capacity and maximum supports before changing the source

Fix one original branch, its derivative vector v, barrier-deficit
vector k and positive-five correction c. Put sigma=13/1215 and

    z_l=k_l*d_l-c_l/5,
    a_l=1-score_l/5,
    vmax=max_l v_l.

Use the gamma=0 capacity dual in each column. Its modified
coefficient v_l*a_l-sigma*v_l/eta_l remains nonnegative:
a_l>=3/5 and eta_l>=1/18 give a_l-sigma/eta_l>=3/5-18sigma>0.

For slots0,...,3 choose the following affine upper supports p_lj
for their original pre-density caps at r=0:

    p_l0=0;
    p_l1=0 for l>=2, otherwise1/5;
    p_l2=0 for l=2, otherwise1/5;
    p_l3=3/20+Delta for l<2, otherwise1/10+Delta. (FS4)

The last support is permitted to exceed1/5. Dropping the original
minimum clip enlarges a cap, so it preserves the required upper
bound. It is not an assertion of feasible mass in that enlarged cap.
The reciprocal eta disappears exactly:

    (v_l*a_l-sigma*v_l/eta_l)*eta_l*p_lj
      =eta_l*v_l*a_l*p_lj-sigma*v_l*p_lj.        (FS5)

Replace dmax in the positive selected-deep credit by the fixed
coordinate d0. It is always a lower support, including at sources
where d0 does not maximize d. Then the four column-hole lower
bounds and the H lower bound are

    Lj=sum_l eta_l*a_l*v_l*(1/5-p_lj)
                     +sigma*min_l[v_l*p_lj+vmax*(d0-d_l)],
    LH=sum_l eta_l*(1+1_(l>=2))*v_l/25
                     +sigma*min_l[v_l/5+vmax*(d0-d_l)]. (FS6)

For the same branch, choose kappa once as a maximizing coordinate
of z at the canonical398 source, breaking ties by the smallest
coordinate. Never change it as the source varies. The original
deep shift has the valid upper support

    sigma*[max_l(z_l+v_l/5)-max_l z_l]
      <=sigma*[max_l(z_l+v_l/5)-z_kappa].        (FS7)

Thus the new fixed branch correction is

    B=min(LH,L0,L1,L2,L3)
                  -sigma*[max_l(z_l+v_l/5)-z_kappa]. (FS8)

Add B directly to the original absolute branch margin, then take
the minimum over all100 branches. Call the result M_i(theta;c)
for a point carrier c. No old optimized average is subtracted to
manufacture a gain function. The fixed supports and every original
branch label are recorded in the certificate.

## 2. The useful coordinate block is jointly(alpha,beta,z)

Hold deficit fixed. Then eta is fixed, while d,n,Delta are affine
jointly in(alpha,beta,z). All quantities inside the minima in(FS6)
are affine in this joint block. The negative maximum in(FS8) is
concave. With the joint block fixed, the same expressions are
concave in deficit, because eta and n are affine and the other
terms are fixed. They are constant in late before adding the old
margin, and concave in the actual carrier weights as well.

The original absolute branch margin is concave in each of these
three source blocks. Its raw357-minus-raw35 term cancels the exact
zero-seven block. The remaining complete raw terms are positive
sums of convex source operators plus affine terms. The original
cofactor maxima have the same convexity. These facts hold jointly
in(alpha,beta,z), since this block enters d and n affinely; they
hold separately in deficit and late. The fixed integer baseline
and positive-five labels are never optimized before this step.

Consequently every corrected branch, and then its minimum over
the100 branches, is concave in each of

    deficit; (alpha,beta,z); late; carrier mixture. (FS9)

This is the property missing in159. It is proved from the formulas,
not inferred from numerical samples. Iterated Jensen uses convex
decompositions of the containing coordinate sets, without assuming
independence of the actual forbidden-family data.

## 3. A complete containing product with36 joint-source vertices

Set p=z-3/4, a=1/4-alpha1, b=1/4-sum_(j>=2)beta_j. Then(FS1)
and the original simplex constraints imply

    p,a,b>=0, p+a+b<=1/18, p<=1/20,
    0<=alpha0<=a,
    beta0,beta1>=0, beta0+beta1<=b,
    beta3,beta4>=0, beta3+beta4<=1/20,
    beta2=1/4-b-beta3-beta4.                    (FS10)

The last inequality on beta3+beta4 is exactly the original forced
first-beta condition beta2>=1/5-b. It is not imposed after scanning.
Conversely(FS10) implies all the stated alpha,beta,z bounds, with
beta2 positive. The deficit and late simplices remain independent
containing factors with six vertices each.

Write delta=1/18 and pmax=1/20. The six(p,a,b) vertices are

    (0,0,0), (0,delta,0), (0,0,delta),
    (pmax,0,0), (pmax,delta-pmax,0),
    (pmax,0,delta-pmax).                         (FS11)

At each such point, choose alpha0 in{0,a},
(beta0,beta1) in{(0,0),(b,0),(0,b)}, and
(beta3,beta4) in{(0,0),(1/20,0),(0,1/20)}.
Remove duplicates when a=0 or b=0. This gives36 distinct generators.
They span the entire joint polytope: first decompose(p,a,b) in(FS11),
holding the fractional split alpha0/a and the two beta shares
fixed; then decompose those splits and the final independent
beta3,beta4 simplex. Every map in this construction is affine in
the factor currently being decomposed. Zero a or b uses its unique
zero split.

Thus6x36x6=1296 source generators, each with18 carriers, suffice
for each new absolute margin. Some generators violate additional
necessary packing conditions and need not be actual families.
They are retained in the containing domain, never silently removed.
The fixed-support formula is defined there even if an optimized
packing LP would have no feasible point.

## 4. Complete exact minimization

The [helper](../../frontier/source-budgets/fixed_support_source_slab.py) evaluates both
heavy margins on this new product, preserving all100 original
branches and18 carriers. It checks4,665,600 branch/carrier values.
At216 independently reconstructed old carrier margins it also
recovers the original full_linear_carrier_frontier API exactly.
At the minimizing canonical point it recovers91's original improved
margin through the actual vector API.

The exact minima are(FS3), attained at canonical398, carrier(1,1),
inside the containing product. Iterated Jensen and(FS9) give

    M_i(theta;pi)>=m_i                           (FS12)

for every actual source and carrier mixture in(FS1) at r=0.
The complete per-source minima, minimizing labels, original support
table and hash of all46,656 new carrier-margin values are in the
[certificate](../../certificates/source_norms/source-budgets/fixed_support_source_slab.json).

For each heavy index there are13,465 scanned source/carrier points
where the fixed-support value is below the old optimized absolute
margin. Therefore the result must be used as an absolute bound.
It does not authorize adding m_i as an extra credit on top of an
old source margin.

## 5. Positive slot loss is paid by the same residual

On the broad slab, eta_l>=1/18, h>=1/2, h0<=2/9 and h1>=5/18.
For0<=r<1/2500 the original five gap entries obey

    G>=241/22500,
    h/(5G)<=2500/241.                           (FS13)

For example eta_min/5-r and(h1-h0)/5-r are at least1/90-r;
h1*(1/10-Delta)-2r is at least1/81-2r. The other two entries
are larger. This proves(FS13) on the complete slab.

The original marker penalty is therefore at most
(2500/241)*vmax. Relative to(FS6), positive r changes the H
correction by at most18sigma*vmax*r. For slot3 the sum of cap
increments, weighted by coefficients no larger than vmax, is
at most

    vmax*r*(h0/h+h1/h1)<=(13/9)*vmax*r.          (FS14)

The coefficient subtraction in(FS5) can only reduce this payment.
All other slot caps are unchanged. Since18sigma<13/9, the entire
fixed branch correction loses at most D_i*r, where
D_i=(13/9)*max_branch vmax. Its source maximum supports and deep
shift do not depend on r.

The existing residual simplex has remaining mass
epsilon=rho-(r+r1)/5>=0. Put P_i=(2500/241)*max_branch vmax.
Because5D_i<P_i,

    D_i*r+P_i*epsilon<=P_i*rho.                 (FS15)

This is one actual budget. It pays the slot movement and unresolved
mass together, rather than assigning a new rho to each effect.
Applying91's original pointwise theorem and(FS12) proves(FS2).

## 6. Exact interface to the complete52 numerator

The original weights are w0=1 and w16=15/17. If N_rest denotes
the other50 original weighted costs, together with the unchanged
signed unit-mass and complete-square terms, then(FS2) gives

    N52<=N_rest+(w0*C0+w16*C16)*S
              -(w0*m0+w16*m16)+(w0*P0+w16*P16)*rho. (FS16)

Alternatively keep the source-dependent M_i(theta;c) before taking
their scalar floor and combine it with the other globally valid
conditional margins in the same fixed-target comparison. The
helper checks that its weights are exactly the first41 entries of
the original52 interface, and records the remaining50 indices.
No original cost, exponent tail, denominator payment or mass term
is omitted by this replacement.

For a completed consumer, take160's inner rectangle
qK>=26/27, rho<=1/20000. The common factor budget gives
Delta<=1/104<1/18, and z<=3/4+1/108<4/5. Its original r bound
is r<=1/4000<1/2500, so(FS2) applies to both K orientations.
The original first-beta labeling is retained.

Keep the actual S coefficient throughout. The heavy coefficient
of S is unchanged; the old favorable term in s-1/4 is discarded.
The new heavy endpoint is evaluated as

    sum_(i=0,16) w_i*(C_i*(53/360)-m_i+P_i/20000),

using the new exact m_i, not assuming an adopted face upper bound
equals C_i*(53/360)-m_i. All other cost-group endpoints and the
entire denominator are unchanged.

| Complete inner comparison quantity | Exact-arithmetic decimal display |
| --- | ---: |
| Previous heavy endpoint | 10.811524542489309 |
| Fixed-support heavy endpoint | 10.109792660999888 |
| New signed numerator endpoint N0 | 35.47225964978622 |
| Complete denominator endpoint d0 | 0.07856224353811789 |
| Remaining actual-S coefficient at the new target | 382.66930239545906 |
| Complete comparison T | 473.11203393433925 |

More precisely, with the original offset C0, mass coefficient M
and cE=1-1/614922, the actual inequalities are

    N_actual<=N0+M*(S-53/360),
    E_actual>=d0+cE*(S-53/360).

Both d0 and D_S=(T-C0)*cE-M are positive. Since S>=53/360 and
T=C0+N0/d0, the full signed target margin is nonnegative. The
exact new target is

    T=1325202118762305505567525403333631490143697472810977131709109
         /2801032363818975245371335532041441856862900603958480240000.

This retains all52 labels, the complete square's actual unit-mass
term, all five denominator objectives, both original raw81
controllers, and every infinite tail. It does not repeat or alter
the completed finite-head scans. The separately callable
complete_inner_comparison function verifies the160 source closure
and reconstructs this aggregation from exact rationals.

The other50 bounds and the denominator have not been extended to
the entire larger source slab by this theorem. Completing that
combination remains open; the global result still requires its
other source and residual branches.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/fixed_support_source_slab.py --check
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/fixed_support_source_slab.py --check-inner
```

The formulas supply an ordinary continuum proof; the program uses
exact rational arithmetic. No Lean theorem or frozen state is claimed.
