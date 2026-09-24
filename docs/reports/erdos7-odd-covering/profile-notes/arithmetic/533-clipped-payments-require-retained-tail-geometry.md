# Clipped payment: scalar survival and an actual middle-mass obstruction

Using the actual numerical labels strengthens the clipped-payment lower
bound enough to exclude its query certificate throughout
1/100<=H(U)<=1/10. The proof first exposes why a cheaper scalar budget
can pass: it retains only seven labels whose actual survivor is too large.
Their sharp survivor bound forces retention on further labels, and two
explicit cost inequalities then rule out the whole stated interval.

[Report532](532-fixed-quota-and-reciprocal-payment-obstructions.md) excludes
the untruncated reciprocal-density payment. This result concerns the
stronger payment truncated to probability one. It still does not exclude
all supported query laws or resolve unrestricted Erdős#7. The mathematics
below is an ordinary proof; no new Lean verification is claimed.

## Result and boundary

Keep report532's actual-family constants and phase-free notation:

    P={3,5,7,11,13,17,19},
    A=212731/110592,
    alpha=7235955529/6075000000000,
    T=565/51,
    h=H(U), a=1-h,
    r_d=Pr(d selected),
    L=integral_(outside U)Pr(S_x subset selected)dH,
    beta=alpha-L>0.

For any actual supported law with density at most1/beta,

    q_d<=c_d(beta)=min(1,1/(beta*d)).

For a selection rule with the required common-law weighted Gibbs bound, replacing report532's full reciprocal-density payment by this clipped bound gives the numerical certificate

    Q_clip=log(h/beta)+sum_(d in M)(1-r_d)*c_d(beta).

The actual covering inequality L+sum_d(1-r_d)/d>=a implies a sharp fractional-knapsack lower bound for this certificate. After enlarging the allowed numerical inventory to all distinct nonunit P-smooth labels, the exact lower envelope is

    F(h,beta)=log(h/beta)+K(1-h-alpha+beta),

with the explicit three-piece function K below. It is a necessary lower bound on Q_clip, not an upper bound or an actual supported-law construction.

In the nontrivial Haar regime alpha<h<=A/T:

- Every beta<=alpha/100 is excluded: F(h,beta)>T.
- Every beta in[alpha/3,alpha] remains feasible for the scalar relaxation: F(h,beta)<11<T, uniformly in h.
- For each h there is one exact threshold beta_*(h) in(alpha/100,alpha/3), defined by F(h,beta_*)=T. The relaxation permits Q_clip<T precisely for beta>beta_*(h).

Thus clipped payment cannot be uniformly excluded by these scalar constraints. A further actual-geometry condition below shows that a sampler must retain reciprocal mass beyond the seven cheapest labels. Two affine cost bounds then exclude the clipped certificate for every actual h in[1/100,1/10]. Realizing low-cost data outside that interval by the same actual original family, joint deletion law, phase choices and valid Gibbs interface remains unresolved.

## First fix the actual numerical inventory

Write t_d=1-r_d, so0<=t_d<=1. The required retained reciprocal mass is

    b=a-L=1-h-alpha+beta.

For a fixed actual inventory M, the exact relaxation is

    K_(M,beta)(b)=min sum_(d in M)t_d*c_d(beta)
                  subject to sum_(d in M)t_d/d>=b,
                             0<=t_d<=1.

If b>sum_(d in M)1/d this is infeasible. Otherwise its cost per unit reciprocal mass at label d is

    d*c_d(beta)=min(d,1/beta).

This is nondecreasing in the numerical label d. An exchange of reciprocal mass from a larger label to an unfilled smaller label therefore cannot increase cost. Fill labels in increasing d until the required mass b is reached, fractionally filling the last label. Beyond d>=1/beta the efficiency is constant, so the order of tied labels is immaterial. This gives the exact finite fractional-knapsack value while preserving numerical distinctness.

Missing small labels in a particular actual M can make this lower bound stronger. The following universal envelope deliberately enlarges M to the entire P-smooth numerical catalogue, so

    K_(M,beta)(b)>=K(b).

No choice of original phases or actual survivor set is supplied by this enlargement.

## The universal envelope uses only seven legitimate labels

For alpha<h<=A/T and0<beta<=alpha, the retained mass satisfies

    659/800<b<1.

The seven smallest distinct nonunit P-smooth labels are

    3,5,7,9,11,13,15.

Define their reciprocal prefix sums

    S4=1/3+1/5+1/7+1/9=248/315,
    S5=S4+1/11=3043/3465,
    S6=S5+1/13=43024/45045,
    S7=S6+1/15=46027/45045>1.

Since S4<659/800 and S7>1, an optimum uses four full labels and then ends at11,13 or15. All seven costs are clipped to1 because beta<=alpha<1/800. Therefore

    K(b)=4+11*(b-S4),   S4<=b<=S5,
         5+13*(b-S5),   S5<=b<=S6,
         6+15*(b-S6),   S6<=b<=S7.                 (CP1)

Each expression is attained in this relaxed catalogue by full retention of all preceding labels and fractional retention of its final label. The unused tail of the catalogue need not be retained.

## The best scalar denominator is beta=alpha

For fixed h, F is continuous and its derivative on each piece is

    partial_beta F=-1/beta+d_j<0,
    d_j in{11,13,15}, beta<1/800.

Thus F strictly decreases with beta. Its minimum over the permitted scalar denominators is at beta=alpha:

    F(h,alpha)=log(h/alpha)+K(1-h).                 (CP2)

This corresponds to L=0 only as scalar data. A positive-leakage interval will remain below target as well; no zero-leakage actual sampler is inferred.

The h derivative of(CP2) is1/h-d_j. Its piece boundaries are

    1-S6=2021/45045<1/15,
    1-S5=422/3465>1/11.

It therefore increases through the seventh-label piece, has its unique maximum in the sixth-label piece at h=1/13, then decreases through the fifth-label piece. The point1/13 lies in the current interval and between the two displayed boundaries. Hence

    max_(alpha<=h<=A/T)F(h,alpha)
      =log(1/(13*alpha))+19346/3465.                (CP3)

This is strictly below10. A rational certificate avoids numerical logarithms:

    exp(1)>8/3,
    exp(1/4)>1+1/4+1/32=41/32,
    exp(17/4)>(8/3)^4*(41/32)=5248/81
                  >1/(13*alpha).

Consequently

    max F(h,alpha)<17/4+19346/3465
                 =136289/13860<10<T.              (CP4)

## A uniform surviving scalar band with positive leakage

If alpha/3<=beta<=alpha, monotonicity of K gives

    F(h,beta)<=F(h,alpha)+log(alpha/beta)
              <=F(h,alpha)+log3.

Since exp(9/8)=exp(1)*exp(1/8)>(8/3)*(9/8)=3, we have log3<9/8. Thus

    F(h,beta)<136289/13860+9/8
             =303763/27720
              <11<T.                              (CP5)

The precise margin below T in this coarse rational certificate is56629/471240>0. In particular beta=alpha/3, with positive scalar leakage L=2alpha/3, survives these necessary inequalities for every h in the stated interval.

## Very small denominators are still excluded

Because F decreases in beta, it suffices to prove the claim at beta0=alpha/100.

For alpha<=h<=1/15, every piece has h derivative1/h-d_j>=0, so

    F(h,beta0)>=F(alpha,beta0).

At this endpoint the retained mass is1-2alpha+alpha/100>399/400, which lies in the seventh-label piece. Therefore

    K(1-2alpha+alpha/100)
      >6+15*(399/400-S6).

The elementary bound exp(1)<49/18<11/4 follows by bounding the factorial tail from its third term by a geometric series. Hence

    exp(9/2)<(11/4)^4*(5/3)=73205/768<100,

where sqrt(11/4)<5/3. Thus log100>9/2, giving

    F(h,beta0)>6+15*(399/400-S6)+9/2
              =2675191/240240
              =T+233047/4084080>T.                 (CP6)

For h>=1/15, we have

    h/beta0>=100/(15*alpha)>16000/3,
    exp(15/2)<3^7*2=4374<16000/3.

Also K(b)>4 throughout the current mass range. Therefore

    F(h,beta0)>15/2+4=23/2>T.                      (CP7)

Together these prove the uniform exclusion beta<=alpha/100. Since F is continuous, strictly decreasing in beta and diverges as beta tends to zero, (CP5)--(CP7) also give the unique threshold beta_*(h) in(alpha/100,alpha/3). On each of the three pieces it is specified exactly by

    log(h/beta_*)+(j-1)
       +d_j*(1-h-alpha+beta_*-S_(j-1))=T,

with its piece-membership inequalities from(CP1).

## Which constraints the surviving scalar data actually satisfy

The preceding construction preserves distinct legitimate numerical labels and0<=r_d<=1, but does not choose actual original phases. To also retain the existing scalar relations lambda>=a and log(h/alpha)>=A-lambda, fix any h>alpha and beta in[alpha/3,alpha]. Start with the at-most-seven greedy retention coefficients attaining K(b). Enlarge the finite numerical inventory by additional distinct P-smooth labels, with retention t_d=0 at each added label. Their reciprocal sums increase to A, so a finite enlargement can satisfy

    lambda>=a,
    lambda>=A-log(h/alpha),
    lambda<A.

The added labels change neither B=sum_d t_d/d=b nor the clipped cost. Assigning the scalar leakage L=alpha-beta then gives L+B=a exactly and preserves all the displayed scalar inequalities. This is feasibility of the specified relaxation, not existence of a family with that survivor mass or a sampler with that actual leakage.

The endpoint h=alpha must not be called an actual finite family: every finite M leaves positive unused reciprocal mass A-lambda, so the known inequality log(h/alpha)>=A-lambda rules it out. Using h=alpha above is only a closure endpoint for a continuous lower-bound comparison.

A particular actual M can lack the cheap labels, and an actual coverage geometry may force larger leakage or couple retention coefficients in ways absent from this relaxation. The following sharp geometry supplies one such additional constraint and excludes the relaxed greedy support as an actual sampler.

## The seven cheap labels cannot by themselves retain enough actual coverage

Let D7={3,5,7,9,11,13,15}. For any globally fixed phases at these seven numerical labels, the actual survivor has Haar mass at least

    kappa=272/1001>1/4.                             (CP8)

To prove this, first impose the pure3 and pure5 originals. Their joint survivor has mass8/15. The9-cylinder can delete at most(1/9)*(4/5)=4/45 from it, and the15-cylinder can delete at most1/15. Thus the3-and5 part retains at least

    8/15-4/45-1/15=17/45.

The three remaining pure labels7,11,13 act on independent CRT coordinates and multiply this mass by

    (6/7)*(10/11)*(12/13)=720/1001.

The product is272/1001. The bound is sharp: choose0 mod3,1 mod9,0 mod5,2 mod15, and0 at7,11,13. In the pure3/pure5 survivor the9 deletion lies in3-root1 and the15 deletion in3-root2, so they are disjoint and both deletion upper bounds are attained. Every retained subset of D7 inherits the same lower bound by filling missing labels with arbitrary phases before applying(CP8).

If a deletion sampler retains originals only in D7, each of its realized retained families therefore has survivor mass at least kappa. The full original U is contained in each retained survivor. For phase-free leakage this yields

    h+L=E H(U_retained)>=kappa,
    L>=kappa-h>3/40>alpha                           (CP9)

throughout h<=A/T<7/40. Hence no such actual sampler has a positive beta. This excludes the support pattern of the greedy scalar minimizer; it does not change the earlier feasibility statement about the weaker scalar relaxation.

More generally define the retained reciprocal mass outside the cheap catalogue by

    B_out=sum_(d in M minus D7)(1-r_d)/d.

For every realized retained subset, the union bound gives

    H(U_retained)>=kappa-sum_(retained d outside D7)1/d.

Taking expectation therefore supplies the additional actual-family condition

    B_out>=kappa-h-L
          =kappa-h-alpha+beta.                     (CP10)

This condition preserves the same actual phases and deletion law; it does not rely on independence among selection events. It shows exactly what the first scalar relaxation omitted: a mandatory amount of retained mass on labels outside the seven cheapest ones. Consequently the feasible band of(CP1)--(CP7) cannot be carried over to the strengthened problem without proof.

## Actual retained geometry excludes the middle mass interval

Split B=B_in+B_out and the clipped cost C=C_in+C_out according to D7. Missing numerical labels can be given retention t_d=0 for these inequalities. Put

    S3=1/3+1/5+1/7=71/105,
    T3=1/17+1/19+1/21=1079/6783.

For the interior labels c_d=1, so

    C_in-9*B_in=sum_(d in D7)t_d*(1-9/d)
                  >=3-9*S3.

Only3,5,7 have negative coefficients; their t_d<=1 bounds those contributions from below. The coefficient at9 is zero and the others are positive.

The three smallest P-smooth labels outside D7 are17,19,21, and all other outside labels are at least25. For those later labels,

    c_d-25/d>=0,

because c_d is either1 with d>=25 or1/(beta*d) with1/beta>800>25. The first three have cost1 and negative coefficients. Hence

    C_out-25*B_out>=3-25*T3.

Combining these two affine lower bounds with B>=1-h-alpha+beta and(CP10) gives

    Q_clip>=log(h/beta)+C0-25*h-25*alpha+25*beta,
    C0=15+16*kappa-9*S3-25*T3
       =45031219/4849845.                          (CP11)

The beta derivative of the right side is-1/beta+25<0. Therefore every0<beta<=alpha satisfies

    Q_clip>=G(h)=log(h/alpha)+C0-25*h.              (CP12)

The function G is concave. On the closed interval[1/100,1/10] it is bounded below by the smaller endpoint value. At the left endpoint, alpha<1/800 gives log(h/alpha)>log8. The positive atanh expansion yields

    log2=2*atanh(1/3)>2*(1/3+1/81)=56/81,
    log8>56/27.

At the right endpoint the same alpha bound gives log(h/alpha)>log80, with

    log80=6*log2+log(5/4)>112/27+2/9=118/27,

using log(5/4)=2*atanh(1/9)>2/9. Thus the endpoint bounds are

    G(1/100)>C0-1/4+56/27
             =T+5364739/174594420,
    G(1/10)>C0-5/2+118/27
             =T+6723907/87297210.                 (CP13)

The second rational lower bound exceeds the first by5/108. Concavity proves

    Q_clip>T for every actual h in[1/100,1/10]

and every phase-free selection law and0<beta<=alpha for which this clipped numerical certificate is proposed. The inequalities themselves need no independence of label selection. If a sampler is to certify a supported law, its separate inside-survivor Gibbs domination must still be proved; this negative statement does not supply that missing validity.

This is a limitation of the clipped uniform-density payment, not a lower bound on the optimal query cost of all actual supported laws. Payments using actual U-cylinder masses, phase-dependent exterior leakage and the remaining mass intervals are not excluded by(CP11)--(CP13).

For this particular clipped, phase-free certificate, a remaining candidate
outside the already sufficient uniform-Haar regime must have

    alpha<h<1/100 or 1/10<h<=A/T,
    beta>alpha/100.

These are necessary conditions, not a construction or a sufficiency
statement. The all-family seven-prime query target and unrestricted
Erdős#7 remain unresolved. The actual-family arguments and affine cost
inequalities are ordinary proofs; the arithmetic checks do not replace them.

The [fixed arithmetic consumer](../../frontier/cover-geometry/clipped_reciprocal_geometry.py)
and [result](../../frontier/cover-geometry/clipped_reciprocal_geometry.json)
check the scalar constants, the actual D7 sharpness configuration on its
45 roots in the3-and5 coordinates, and the support-line margins. They do
not enumerate all original phases or verify the general probability proof.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/clipped_reciprocal_geometry.py
```
