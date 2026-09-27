[Index](../../marked_head_profile.md) · [Original height lift](../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md) · [Previous scalar boundary](439-actual-residual-lifting-and-exact-free-coordinate-cost.md) · [Common test boundary](440-joint-test-profiles-as-composable-boundaries.md)

# Joint integer partial loads improve a height lift with an arbitrary fixed cofactor

Ordinary mathematical deduction, not Lean certification. The hypothesis and actual-family support contract are exactly Chapter09 H1. An arbitrary fixed cofactor is retained with all its divisors and mixed tests. No new prime is introduced during the lift and no actual-cover extraction is supplied. All complete test layouts keep independently variable original phases. One probability is fixed before those phases are tested.

## Statement

Let M>=1 with gcd(M,35)=1, Q0=175M=5^2*7*M, and Q=5^K*7^J*M, K>=2, J>=1. Let the actual forbidden family have distinct nonunit original moduli dividing Q. Let mu be a probability avoiding every actual forbidden class whose modulus divides Q0, and suppose Gamma_Q0(mu)<=C. Gamma includes EVERY divisor of Q0, including mixed cofactor divisors. Define n5=K-2 and n7=J-1, and

    u5=sum_{t=1}^{n5}5^-t, v5=sum_{t=1}^{n5}(2t-1)5^-t,
    u7=sum_{t=1}^{n7}7^-t, v7=sum_{t=1}^{n7}(2t-1)7^-t.

The following bounds are valid for C>=1; the numerical applications use 4<=C<=9, where the retained affine faces improve the original scalar estimates. Put q=C-1 and

    lambda = u5*q/8 + u7*(C+8)/12 + u5*u7*q/35,

    A = C + 2*u5*(3*q/8) + 2*u7*(C/2)
          + 2*u5*u7*(6*q/35)
          + v5*q/8 + v7*C/4
          + 2*u5*u7*(17*q/96)
          + 2*v5*u7*(2*q/35)
          + 2*u5*v7*(3*q/35)
          + v5*v7*q/35.

If lambda<1, the actual complete family has a survivor, and conditioning the uniform fibre extension of mu on actual complete survival gives one probability mu' with

    Gamma_Q(mu') <= (A-lambda)/(1-lambda).                 (I1)

The conditioned coarse marginal can change. No positive survival in every coarse fibre or preservation of an arbitrary prescribed marginal is asserted.

For the finite lift 175M -> 6125M=5^3*7^2*M, this simplifies to

    A=(81289*C-11989)/58800,
    lambda=(1109*C+2041)/29400.                           (I2)

At C=46/9,

    Gamma_(6125M)(mu') <= 3492627/390434
                     = 9 - 21279/390434 < 9.             (I3)

Uniformly in all finite K,J, substitute

    (u5,v5,u7,v7)=(1/4,3/8,1/6,2/9).

All coefficients multiplying these sums are nonnegative for C>=1. Thus

    A=(8667*C-1627)/5760,
    lambda=(467*C+793)/10080.                            (I4)

At the sharp minimum-source scalar C=68/15, the resulting conditional certificate is

    Gamma_Q(mu') <= 3780053/430196
                 = 9 - 91711/430196 < 9.                 (I5)

The all-height affine certificate is <=9 precisely when

    C <= 348893/75613 = 4.6141933265...                   (I6)

within the stated positive-denominator regime; use strict inequality for a strict target below nine. For the finite lift the corresponding threshold is 169511/33011=5.1349853079.... These are certificate thresholds, not lower bounds on the true minimax. In particular the current C=46/9 seed does not satisfy the all-height threshold. The value 68/15 is not asserted to be a universal seed theorem: report435 proves it for its minimum-source class at M=1 and as an obstruction to stronger universal scalars, not for arbitrary cofactors.

The result is useful as a height-extension implication with arbitrary retained cofactor tests, rather than a new noncoverage theorem for families supported only on primes5 and7. The latter two-prime domain already has stronger direct survivor bounds in the project.

## One-space moment data

Group fine labels by the excess vector above heights (2,1), exactly as in H1, retaining the entire M-divisor label. Their reduced coarse loads have four types; in the label list below every entry is multiplied by every divisor m of M:

    0:   full coarse layout A0, label shapes (1,5,25,7,35,175);
    5:   partial load A5, label shapes (25,175);
    7:   partial load A7, label shapes (7,35,175);
    57:  partial load A57, label shape (175).

All loads are nonnegative integers and A0>=1. Different excess vectors of one type may have different independent phases. For an actual forbidden subfamily some labels can be absent. No proof below assumes bounds 2,3,1 for the partial loads; those bounds hold only when M=1. In particular A57 is not assumed to be an indicator.

For a partial load F of type S, projecting its classes down the saturated prime axes gives a complete coarse layout of load at least D_S F and at least one. Here (D0,D5,D7,D57)=(1,3,2,6). Consequently on the SAME probability mu,

    E g_D(F)<=C,   g_D(z)=max(1,D^2*z^2).                 (I7)

The completion can differ with the tested partial layout; Gamma's universal quantifier supplies all these inequalities on that same mu. It does not select a different probability per layout.

The exact integer first-moment inequalities are

    F5 <= (g3(F5)-1)/8,
    F7 <= (g2(F7)+8)/12,
    F57 <= (g6(F57)-1)/35.                               (I8)

The first and third use D^2*z^2-1 >= (D^2-1)z for integer z>=1, with the zero case direct. For the middle inequality, z=0 is direct; at z>=1 it is 4(z-1)(z-2)>=0, valid for every integer. It is equality at 1 and 2, replacing the curved Cauchy estimate by the relevant integer convex-envelope face.

For ANY two loads of the indicated types on mu (including two independently phased copies of a type), an upper matrix for their mixed moments is

| types | 0 | 5 | 7 | 57 |
|---|---:|---:|---:|---:|
| 0 | C | 3q/8 | C/2 | 6q/35 |
| 5 | 3q/8 | q/8 | 17q/96 | 2q/35 |
| 7 | C/2 | 17q/96 | C/4 | 3q/35 |
| 57 | 6q/35 | 2q/35 | 3q/35 | q/35 |

This is an entrywise upper matrix, not asserted positive semidefinite and not asserted simultaneously attainable. Entrywise bounds suffice because every fibre-count coefficient is nonnegative.

The nontrivial entries have short pointwise proofs. A reusable general inequality, for positive integer d, integer D>=2, and nonnegative integers a,b, is

    (D^2-1)g_d(a) + (D^2+1)g_D(b) - 2D^2
       >= 2*d*D*(D^2-1)*a*b.                            (I9a)

If either argument is zero, the left side minus the right side is a nonnegative coefficient times the other g-value minus one. If both are positive, its exact difference is

    (D^2-1)(d*a-D*b)^2 + 2D^2(b^2-1) >= 0.

Thus, whenever both g-moments are <=C on one probability space,

    E[a*b] <= D*(C-1)/(d*(D^2-1)).                      (I9b)

This gives (0,5) with (d,D)=(1,3), (5,5) with (3,3), and every type57 entry with D=6 and d=1,3,2,6. No maximum-load assumption or indicator assumption is used. For example, for a>=1 and integer b>=0 the (0,5) inequality is equivalently

    24*a*b <= 4*a^2 + 5*g3(b) - 9.                       (I9)

If b=0 this is 4(a^2-1)>=0. If b>=1 the difference is
4(a-3b)^2+9(b^2-1)>=0. Taking expectations gives the (0,5) entry.

For nonnegative integers a,b,

    16*a*b <= g3(a)+g3(b)-2.                             (I10)

With a,b>=1 the difference is 9(a-b)^2+2ab-2>=0; when either is zero it is nonnegative directly. This gives the (5,5) entry without treating the two partial layouts as the same layout.

The genuine cross-axis improvement uses integrality without a size bound:

    96*a*b <= 9*g3(a)+8*g2(b)-17,
          a,b nonnegative integers.                    (I11)

If a=0 or b=0 the difference is respectively 8(g2(b)-1) or 9(g3(a)-1), both nonnegative. For a,b>=1 it is

    32(b-3a/2)^2 + 9a^2 -17.

For a>=2 this is positive. For a=1, integer b is at distance at least 1/2 from 3/2, so the difference is at least 8+9-17=0. Equivalently, for a=1 the difference is 32(b-1)(b-2)>=0. Thus E(A5*A7)<=17q/96. This retains their joint realization on mu rather than multiplying separately optimized marginal conclusions.

The (0,0), (0,7), (7,7) entries follow from Cauchy and E A0^2<=C, E A7^2<=C/4. Every type57 entry instead follows from I9b. These arguments keep all independent phases and all mixed cofactor labels.

As a check on the strength and its limit, the (5,7) moment relaxation is attained for 1<=C<=9 by a joint abstract distribution with masses

    Pr[(a,b)=(0,0)]=1-q/8,
    Pr[(a,b)=(1,1)]=7q/96,
    Pr[(a,b)=(1,2)]=5q/96.

Both g-moments equal C, and E ab=17q/96. This only certifies sharpness given the two retained moment constraints. No claim that this abstract coupling is realized by arithmetic source layouts is made.

## Summing the fine load and actual conditioning

The conditional intersection of two fine classes with excess vectors t,s is at most the indicator of their actual coarse intersection times 5^-max(t5,s5)*7^-max(t7,s7). Sum first over each pair of coarse groups, then over excess vectors. By the mixed-moment matrix the aggregate coefficient matrix is

    W = [[1,       u5,       u7,       u5*u7],
         [u5,      v5,       u5*u7,    v5*u7],
         [u7,      u5*u7,    v7,       u5*v7],
         [u5*u7,   v5*u7,    u5*v7,    v5*v7]].

The sum of W_ij*M_ij is exactly A. Incompatible extra-digit phases only reduce intersections. Therefore every full fine test layout has second moment <=A under the one uniform extension nu.

For the actual excluded classes, the single-class fibre weights and (I8) give excluded union mass b<=lambda. These are the original distinct labels; reduced moduli within each excess vector remain distinct as in H1. Condition nu outside the actual forbidden union. Every complete test load has square at least one, so

    E_mu' L^2 <= (A-b)/(1-b) <= (A-lambda)/(1-lambda),

where monotonicity uses A>=1. This proves I1 and actual survival when lambda<1. It does not give free access to nonexistent fibre points or bypass the actual-family seed premise.

## Relation to the previous scalar obstruction

Report439's obstruction remains correct for its displayed H1 scalar formula: at C=68/15, improving lambda alone leaves the positive gap 263/56700 in A_old+8lambda-9. The new result changes the square-load estimate, using integer and cross-axis information discarded by independent H2 plus Cauchy. Therefore I5 supersedes that formula as the best supplied certificate without reversing the earlier conclusion about the older formula.

No unrestricted Erdős #7 conclusion follows: the necessary supported seed on every intended actual residual and a universal C below I6 remain separate obligations. The arbitrary fixed cofactor's mixed costs are included in the hypothesis Gamma_Q0(mu)<=C; a bound only on a 175 projection cannot substitute for that hypothesis.

## The four moment budgets do not suffice at C=46/9, even with a joint law

The entrywise matrix need not be jointly attainable. However, optimizing the four load types jointly while retaining only I7's four moment budgets still cannot force the all-height target below nine. The following witness is a single joint probability, not four separately chosen optimizers.

Write X=(A0,A5,A7,A57), with A0 a positive integer and the other entries nonnegative integers. For the coefficient matrix W above put

    Phi(X)=X^T W X,
    D(X)=u5*A5+u7*A7+u5*u7*A57.

Here D is the load-derived first-moment deletion majorant, not an assertion that an actual excluded union attains it. At the all-height coefficients (u5,v5,u7,v7)=(1/4,3/8,1/6,2/9), take the following four atoms:

| X | Probability |
|---|---:|
| (1,0,1,0) | 35/72 |
| (3,1,1,0) | 111/280 |
| (3,1,1,1) | 47/1890 |
| (3,1,2,1) | 5/54 |

The masses sum to one, and on this SAME space,

    E g1(A0)=E g3(A5)=E g2(A7)=E g6(A57)=46/9.

Indeed if p=37/72, z=37/315 and t=5/54, then A0=1+2*A5, Pr(A5=1)=p, Pr(A57=1)=z, and Pr(A7=2)=t with A7 otherwise1. The four expectations are respectively1+8p,1+8p,4+12t,1+35z. All three first-moment bounds I8 are simultaneously attained. The mixed moments also obey every entry of the I7-derived matrix, since those inequalities hold for any such joint law.

Direct evaluation of the joint quadratic form gives

    E Phi=3948953/544320,
    E D=28619/90720,
    E(Phi+8D)=1064533/108864
              =9+84757/108864 >9.                      (I12)

In addition D(X)<=5/8 on every atom and E D<1. Thus even replacing D by its pointwise truncation min(D,1) does not change this witness. The failure is not caused by a nonpositive conditioning denominator.

This already occurs at finite heights. With n5=n7=2, hence Q=5^4*7^3*M, the same joint law and the finite geometric coefficients give

    E(Phi+8D)=4443137/463050
              =9+275687/463050 >9.                     (I13)

To view it as a model with all excess vectors, assign to each vector the random variable of its support type. Every group is then defined on one probability space, and every I7 moment condition continues to hold. This shows that merely retaining all correlations or using a better joint dual of these four budgets cannot prove a universal bound E(Phi+8D)<9 at C=46/9: the displayed common distribution is feasible and violates that target. It is a lower witness for the moment relaxation, not a claim that its objective is the optimum.

The witness does NOT construct an arithmetic source, actual independent residue layouts, a legal forbidden family, or a realizable excluded union of mass E D. Real arithmetic completion and intersection relations can impose additional constraints absent from this relaxation. No such extra relation is established here, so this result rules out only the four-budget certificate route; it neither refutes the desired supported-law theorem nor obstructs a proof retaining further original-label information.

For a broader exact version, the same four atoms have respective masses

    (9-C)/8, 27(C-1)/280, (128-23C)/420, (C-4)/12

for4<=C<=128/23. All four g-moments equal C, and

    E(Phi+8D)=(113105*C+13315)/60480.

Consequently this feasible family reaches nine at C=106201/22621 and exceeds nine above it within that interval. This is a necessary limitation of the retained-moment model, not a universal arithmetic seed threshold.

## Verification

[The exact companion](../../frontier/cover-geometry/integer_partial_load_height_lift.py) uses only Python's standard library and exact Fraction arithmetic. It checks finite controls of the universal pointwise identities, symbolic affine coefficient identities, moment-relaxation sharpness witnesses, exact target margins, and monotonicity prerequisites. It writes a result summary, not a proof-state claim. The displayed nonnegative-square proofs handle unbounded integer loads; finite checks alone do not certify those universal conclusions, source extraction, or Lean verification.

Run from the repository root:

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/integer_partial_load_height_lift.py
