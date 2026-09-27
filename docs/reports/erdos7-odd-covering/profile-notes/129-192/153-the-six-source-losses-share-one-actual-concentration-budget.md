[Index](../../marked_head_profile.md) · [Original concentration](../065-128/106-the-actual-denominator-shares-the-carrier-mass-residual.md) · [Signed product mass](150-signed-source-monotonicity-strengthens-the-product-mass-bound.md) · [Complete raw prices](140-ten-adopted-quadratic-costs-share-a-uniform-source-neighborhood.md)

# The six source losses share one actual concentration budget

For the original source concentration qK>=1-sigma,0<=sigma<1/2,
choose the distinguished orientation as in106. Its six factor losses
obey the single inequality

    u_alpha+u_z+u_beta+u_d+u_l+u_pi<=sigma/(1-sigma). (JB1)

This uses the actual two-orientation formula for qK and the same
normalized carrier law as S0. It is stronger than separately bounding
each loss by sigma. As a result, nonnegative source-error prices may
be combined before paying their largest coefficient from(JB1).

The theorem does not assert that the bound is sharp, and does not
identify source-coordinate distance with total variation between
survivor measures. Original test labels and all infinite tails in
an existing raw-price theorem are unaffected.

## 1. Retain the contribution of the opposite orientation

In the notation of148 and150, put

    A=(1-u_alpha)*(1-u_z)*(1-u_beta)=1-y,
    qK=A*t,
    t=d1*l1*pi1+d2*l2*pi2.                       (JB2)

The selected orientation has

    d1=1-u_d, l1=1-u_l, pi1=1-u_pi.

The deficit and late barycentric weights each sum to at most1;
the original carrier weights are normalized. Therefore the opposite
orientation satisfies

    d2<=u_d, l2<=u_l, pi2<=u_pi.

Its contribution cannot be bounded as a fresh independent mass.
Substitution gives the sharper joint inequality

    t<=(1-u_d)*(1-u_l)*(1-u_pi)+u_d*u_l*u_pi
       =1-B,
    B=u_d+u_l+u_pi-u_d*u_l-u_d*u_pi-u_l*u_pi.     (JB3)

The cubic terms cancel exactly. Since qK>=1-sigma and A=1-y,

    0<=y<=sigma,
    B<=(sigma-y)/(1-y).                          (JB4)

The orientation lemma also gives each individual loss at most sigma.
For any two of the last three losses,

    u_i*u_j<=sigma*(u_i+u_j)/2.

Summing the three pairs shows that

    B>=(1-sigma)*(u_d+u_l+u_pi).                 (JB5)

This is a relation between actual concentration factors. No product
law for random source variables is introduced.

## 2. Add the common-factor loss only once

All three common factors are positive. The elementary product bound

    1/A=product_i[1+u_i/(1-u_i)]
       >=1+sum_i u_i/(1-u_i)>=1+sum_i u_i

implies

    u_alpha+u_z+u_beta<=y/(1-y).                 (JB6)

Combining(JB4)--(JB6) gives

    sum_all_six u
      <=y/(1-y)+(sigma-y)/[(1-y)*(1-sigma)]
       =sigma/(1-sigma).

This proves(JB1). If0<=sigma<=delta<1/2, monotonicity permits the
uniform replacement sigma/(1-sigma)<=delta/(1-delta).
For any six nonnegative prices p_i it follows that

    sum_i p_i*u_i<=max_i(p_i)*delta/(1-delta).    (JB7)

When several errors are incurred together, add their price vectors
before taking the maximum. Taking a separate maximum for each error
is still a valid upper bound, but can lose the common budget benefit.

## 3. Norms for the same face projection

Use the K-face projection of106. On the actual first-beta domain one
may instead use142's valid construction, deleting root0 beta mass
and adding the missing root1 mass to the original first-beta cell.
Both constructions satisfy the following factorwise estimates:

    N:=||n-n*||1
      <=u_alpha/6+5u_z/36+u_beta/18+u_d/9+u_l/36,
    E:=||eta-eta*||1<=u_d/9,
    D:=||d-d*||infinity<=(u_alpha+u_z+u_beta)/4.   (JB8)

For N, expand the source products exactly as in106, with each root
occurring at most three times. For E, eta=(1-deficit)/9 and the
deficit L1 difference is at most u_d. For D, the changes in z, alpha
and each beta coordinate are at most u_z/4,u_alpha/4,u_beta/4.
The beta bound follows either from root1 normalization or from the
explicit missing-mass filling; the latter still requires142's
actual first-beta hypotheses when its admissibility is used.

Consequently(JB1) gives uniform bounds

    N<=delta/[6*(1-delta)],
    E<=delta/9,
    D<=delta/[4*(1-delta)].                      (JB9)

The E bound retains the smaller individual inequality. No continuity
claim for an optimized dual or an entire survivor measure is needed.
Other hypotheses of a downstream marked-source theorem, including
its availability and packing guards, remain its own obligations.

For a complete raw-source price L_N*N+L_E*E+L_D*D, the corresponding
six-coordinate vector is

    alpha: L_N/6+L_D/4,
    z:     5L_N/36+L_D/4,
    beta:  L_N/18+L_D/4,
    d:     (L_N+L_E)/9,
    l:     L_N/36,
    pi:    0.                                   (JB10)

Apply(JB7) to this vector for a joint bound. In particular, when the
raw price already includes every polynomial and geometric tail as
in140, (JB10) retains them: it changes the source budget, not the
test function or its exponent inventory.

## 4. The signed carrier-to-raw mass difference also has a joint price

Keep the exact identity

    S-s=-(score.n+R)/5+rho,
    (S-s)*=53/360-1/4.

Because score.n>=(1-u_pi)c*.n, c*.n*=2/9 and c* has only zero-one
entries,

    c*.n*-score.n<=N+2u_pi/9.

The complete cap estimate148 gives

    R*-R<=(u_alpha+u_beta+2u_d)/72.

Therefore

    (S-s)-(S-s)*<=rho+N/5
                        +(u_alpha+u_beta+2u_d)/360+2u_pi/45. (JB11)

Insert(JB8). The resulting six prices, in the order alpha,z,beta,
deficit,late,carrier, are

    (13/360, 1/36, 1/72, 1/36, 1/180, 2/45).

Their maximum is2/45, so

    S-s<=53/360-1/4+2delta/[45*(1-delta)]+rho.    (JB12)

This can replace146's7delta/45 source price where its original
S-s interface is used. If a complete signed comparison instead
retains S and s separately, it must derive that comparison from the
original expression; one may not claim both cancellation savings
for the same already-eliminated mass term.

For that separate use, the raw source also has the elementary global
floor

    s=[z*sum w-sum_r alpha_r*(root sum w)_r
                       -sum_j beta_j*w_j]/9-sum late
      >=[(3/4)*(9/2)-(1/4)*3-1/4]/9-1/72=1/4.   (JB13)

This uses only the original source caps. It is distinct from146's
S0>=53/360, and neither one alone is a floor for the final AP survival
denominator. Positive coefficients must be checked before both floors
are substituted into a signed target inequality.

The [helper](../../frontier/comparison-bounds/joint_concentration_loss_budget.py) exports
the total-loss bound, nonnegative weighted prices and the source norm
price conversion. Its exact checks reconstruct(JB3), retain all six
coefficients, verify the auxiliary-y cancellation and(JB13), and
produce examples without treating them as a continuum proof.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/joint_concentration_loss_budget.py --check
```

These are ordinary actual-source inequalities with rational algebra
checks. A full numerator/denominator consumer is required before
they improve a comparison. No new global K, Lean verification or
unrestricted Erdos7 resolution is asserted in this section.
