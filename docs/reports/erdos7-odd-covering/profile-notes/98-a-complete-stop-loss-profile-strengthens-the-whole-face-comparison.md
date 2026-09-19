[Index](../marked_head_profile.md) · [Common seven bridge](83-common-seven-hinges-on-both-complete-k-control-faces.md) · [Surviving-tail peeling](86-peeling-surviving-tails-improves-the-k-face-comparison.md) · [Complete vector comparison](97-vector-source-margins-improve-the-complete-face-comparison.md)

# A complete stop-loss profile strengthens the whole-face comparison

For every independently labelled complete original357 test A on either
actual saturated K-control beta face, write

    H_t=integral_survivor(A-t)_+.

The following upper bounds hold uniformly over the entire actual faces,
with r=rho=0 and survivor mass D=53/360. Every exponent tail is complete.

| t | Selected old-tail prefix length | Uniform upper U_t |
| --- | ---: | ---: |
| 1 | Complete mean identity | 443/900 |
| 2 | 1 | 3869/10500 |
| 3 | 2 | 86623/330750 |
| 4 | 3 | 938213/4630500 |
| 5 | 4 | 1523903/9724050 |
| 6 | 4 | 89710847/680683500 |
| 7 | 4 | 547475903/4764784500 |
| 8 | 4 | 388664263/3705943500 |

The t=4,5 entries reuse86's same certified formulas. The five other
nontrivial thresholds are evaluated by625000 exact head/projection/LP
checks. No source distribution or beta interpolation is guessed.

The common profile gives exact upper bounds for all41 linear-growth AP
costs. Taking each minimum with97's existing vector bounds, then legally
substituting those bounds once into the52 existing all-load majorants,
improves38 costs. The final complete comparison is

    N<=35.29386893590073135079943897679...,
    d>=40455251803/517708422000,
    C0+N/d<=473.2520067260898808543564636440... .       (SL1)

Compared with97's485.96887440471189263903..., the face comparison drops
by12.71686767862201178467.... All52 cost terms, the negative mass
coefficient, the complete square complements,97's quadratic improvements,
and the entire86 denominator remain in the calculation. The final
majorant substitution supplies zero additional gain in this instance.

This is an ordinary full-tail proof on the actual saturated faces. It
does not supply an off-face neighborhood or a new global K bound, remains
above403, and is not a Lean proof or an unrestricted Erdős7 solution.

## 1. Peel the unselected load on the actual survivor

Retain the six distinct original zero-seven labels

    B=I1+I3+I9+I5+I15+I45,

and order four further distinct zero-seven labels as

    (M1,M2,M3,M4)=(25,27,75,81).

Their arbitrary-residue surviving cylinder caps from75 and86 are

    (c1,c2,c3,c4)=(2/125,7/270,4/375,7/810).          (SL2)

The complete surviving zero-seven tail outside B has cap163/1800.
For any0<=k<=4, let X_k=sum_(i=1..k)I_(M_i), and put all other
zero-seven labels into Y. Summing their individual cap series gives

    integral_survivor Y<=R_k=163/1800-sum_(i=1..k)c_i. (SL3)

This removes assigned terms from a known sum of cap coefficients; it
does not subtract an upper bound from an unknown actual total.

Among the positive-seven labels, retain every unit7^e and the original
labels21 and35 in R. Put every other positive-seven label in Z. The
complete raw source cap sum from83 gives

    integral_survivor Z<=Zplus=779/12600.            (SL4)

All five sets of original labels defining B,X_k,Y,R,Z are disjoint.
Their residue supports may overlap, and no equality between independently
chosen residues is used. The increasing1-Lipschitz hinge h_t(v)=(v-t)_+
gives pointwise

    h_t(B+X_k+Y+R+Z)<=h_t(B+X_k+R)+Y+Z.             (SL5)

Thus the tails in(SL3),(SL4) are paid directly on the survivor before
the common raw seven bridge is applied.

## 2. The same seven bridge works for every integer threshold

Fix an old-coordinate rectangle(c,s). The independent old projections
of21 and35 are a ternary root T and a first-five slot F. Write

    m(c,s)=1_(ROOT(c)=T)+1_(s=F), 0<=m<=2.

At this old point the retained positive-seven list contains m+1 original
depth-one indicators, followed by one original unit indicator at every
depth e>=2. Each depth-e term has its complete normalized seven cap
6/(5*7^e). For arbitrary ordered indicators J_i and an integer q>=0,

    (sum_i J_i-q)_+<=sum_(i>q)J_i.                  (SL6)

For q=(t-v)_+, summing the entire remaining geometric series in(SL6)
gives the nonnegative bridge

    g_(t,m)(v)=1/[5*7^max((t-v)_+-m,0)]
                       +(6/35)*max(m-(t-v)_+,0).    (SL7)

If q<=m, its value is the remaining(m+1-q) depth-one caps plus the
complete depth>=2 tail. If q>m, its value is the geometric series
starting at depth q-m+1. Hence(SL7) holds for every integer t>=1,
without any compatibility assumption on the original seven residues.

Let Lambda be the original raw35 source and mu its actual surviving
marginal. On the saturated faces,83 supplies the selected-deletion
density

    mu<=w*Lambda,
    w(c,s)=1-[1_(c>=2)+1_(c=1)+1_(s=H)
                                 +1_(c>=2,s=H)]/5,
    w>=2/5.                                        (SL8)

After(SL5), the same measure argument as83 bounds the retained integral
by the raw source integral of

    f_(t,w,m)(v)=w*h_t(v)+g_(t,m)(v).                (SL9)

This uses mu<=w*Lambda only for the nonnegative old hinge term. It does
not replace the actual surviving measure by w*Lambda or put the already
peeled Y term back inside g.

The function(SL9) is increasing and integer-convex. Before the threshold,
its forward increments are the geometric g increments, increasing to
6/35. At and beyond the threshold they equal w>=2/5>6/35. This proves
the assertion for every integer t, including thresholds above5; it is
not inferred from checks at t=4,5. The verifier independently checks all
used finite increments and their exact affine continuations.

## 3. A finite common-head functional bounds the complete hinge

For any increasing integer-convex f and arbitrary indicators I_i,

    f(B+sum_(i=1..k)I_i)
       <=f(B)+sum_(i=1..k)I_i*[f(B+i)-f(B+i-1)].     (SL10)

When I_i=1, the preceding indicators contribute at most i-1. Monotone
forward increments therefore bound its true contribution by the ith
displayed increment. This proof neither nests the indicators nor changes
their original labels.

Apply83's original source LP U_L to f(B), and its original cylinder
operators P_(a,b) to the nonnegative increments in(SL10). These operators
retain the same arbitrary original source residues, first-beta exclusions
and three group masses

    (1/36,1/12,5/36).                               (SL11)

The resulting general generator is

    H_t<=Zplus+R_k+max_(layout,T,F) {
         U_L(f_(t,w,m)(B_layout))
         +sum_(i=1..k)P_(M_i)(f_(t,w,m)(B_layout+i)
                              -f_(t,w,m)(B_layout+i-1)) }.
                                                        (SL12)

The original B layout, T and F stay the same through the head and all
selected increments inside this maximum. The individual P operators are
valid arbitrary-cylinder bounds for independently labelled25,27,75,81.
The maximum ranges over all12500 original head layouts and all10 choices
of T,F; no common maximizing residue is asserted to exist in a source.

The first-beta source mass remains in the root1 group constraint of
(SL11). Therefore every actual distribution of the remaining beta budget
is feasible in this one LP. Permuting root1 cells transports its raw,
descendant and density tables; the original root0-cell exchange transports
the same proof to the other face. This supplies the whole-face scope
without interpolating independently optimized beta points.

Choose k=min(t-1,4) for2<=t<=8. For t=4,5, (SL12) is exactly86's
surviving-tail formula, with R_3=41/1080 and R_4=19/648. Reuse those
certified maxima. For t=2,3,6,7,8, the new program enumerates the same
original heads and projections, checking a feasible primal and matching
dual for every LP and exact integer-scaled cylinder increments. These
625000 checks give the table above. U1=L-D=443/900 follows instead from
the exact mass and complete first-moment upper bound L=1151/1800.

For infinite label families apply(SL5),(SL6),(SL10) to finite prefixes
and pass to the increasing complete loads. The complete cap sums
(SL3),(SL4) and the exact geometric series in(SL7) dominate all remaining
tails. No exponent cutoff substitutes for these bounds.

## 4. One profile controls every linear-growth AP cost

Every one of the41 original linear-growth AP cost functions is increasing,
integer-convex, and affine by load8. The program checks those facts from
their exact source functions and pinned affine-tail metadata, including
each finite transition. Set

    d1=f(2)-f(1),
    kappa_j=f(j+1)-2*f(j)+f(j-1)>=0, 2<=j<=8.

Successive summation of the first differences gives, for every integer
v>=1,

    f(v)=f(1)+d1*(v-1)+sum_(j=2..8)kappa_j*(v-j)_+. (SL13)

The code verifies the finite values and matches both slope and intercept
of the entire affine tail. Thus(SL13) is not a finite interpolation.
After integration on the same survivor,

    integral f(A)<=f(1)*D+d1*U1+sum_(j=2..8)kappa_j*U_j. (SL14)

Every multiplier of U_j is nonnegative. Apply(SL14) separately to each
independently labelled original AP test. Sharing one valid uniform upper
profile across different tests does not identify their residues.

For each of the52 costs, take the minimum of(SL14), where applicable,
and97's already proved bound. This retains whichever vector estimate is
stronger, including all five quadratic bounds and six raw81 bounds. Use
that fixed vector once in the existing52 all-load majorants, as in97;
their finite prefixes and complete polynomial tails are checked again.
This last substitution is legal and yields no further improvement here.

Against97, the38 improved costs decrease the full numerator by

    161078809575885301992191332306540530041
    /162094612438562866876518705000000000000
    =0.993733271899690221395391746262... .            (SL15)

For comparison only, using(SL14) against86 without97's intervening vector
improvements gives a linear numerator gain1.00579634143214088408.... That
number is not additionally deducted in(SL15).

## 5. The final comparison retains every signed and infinite term

The original complete numerator remains

    N=r_mass*D+sum_(i=1..52)w_i*cost_i+c_square*(374/75),
    r_mass<0, w_i>0, c_square>0.                     (SL16)

All52 terms are present. The negative mass uses the exact same D, and the
complete square-complement coefficient retains both original tails.
Substituting the valid per-cost upper bounds in(SL16) gives

    N=8928394385235033599996847474534270323010312604177
       /252972956902243138190838916958250000000000000000.

The unchanged positive denominator lower bound is reconstructed from
the entire AP11 expansion, including tail moments5/43923 and17/29282,
and from86's exact coefficient formula. With the unchanged offset
C0=185694867601/8599322160, the exact comparison upper bound is

    45962432384428293421073188005370157018935603324321601
    /97120417306609665359541226329029902125000000000000.

This proves(SL1). The same source measure underlies every integrated
bound; simultaneous attainment of their separate upper bounds is not
required. No statement is made for a neighborhood where r or rho is
positive.

## 6. Why the finite profile does not replace the quadratic tail

For an integer-valued A>=1, its exact remaining second-factorial tail is

    T_J=sum_(j>=J)H_j
       =(1/2)*integral(A-J)_+*((A-J)_++1).           (SL17)

Writing L_mu=integral A and Q_mu=integral A^2 gives the identity

    T_J=(Q_mu-L_mu)/2-sum_(j=1..J-1)H_j.            (SL18)

The new profile bounds H_j from above. Subtracting those upper bounds
in(SL18) gives the wrong direction for an upper bound on T_J. Therefore
the existing quadratic and raw81 estimates are retained. A stronger
quadratic continuation needs valid control of the remaining factorial
tail or other information with the required inequality direction; the
finite stop-loss table alone does not supply it.

## Reproduction

[whole_face_stop_loss_generator.py](../frontier/whole_face_stop_loss_generator.py)
reuses83's head, source LP and arbitrary-cylinder definitions,86's complete
surviving tails and calibrated fourth/fifth hinges, and97's current52-cost
bounds. The[exact certificate](../certificates/source_norms/whole_face_stop_loss_generator.json)
retains the complete threshold profile, maximizing LP witnesses, the
digest of all625000 new objective evaluations,41 exact affine expansions,
52 majorants and the signed comparison identity.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/whole_face_stop_loss_generator.py --check
```
