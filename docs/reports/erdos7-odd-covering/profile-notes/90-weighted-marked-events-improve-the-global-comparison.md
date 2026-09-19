[Index](../marked_head_profile.md) · [Linear source payments](47-six-linear-tests-share-the-survival-carrier.md) · [True conditional costs](49-full-linear-and-quadratic-carriers-refine-the-frontier.md) · [Broad source packing](85-a-broad-five-slot-source-deletion-tradeoff.md) · [Marked identity cancellation](89-a-marked-event-cancellation-improves-global-k.md)

# Weighted marked events improve the global comparison

The original modulus5 cancellation applies to every one of the41
linear costs in the complete AP inventory. A fixed set of22 positive
improvements gives the new global bound

    K<=12186762786791794283131839768461516202460812017109414958397
          /23921056002762015270933574636024044150670381020000000000
      =509.4575584533000853637603... .                    (WM1)

This improves89 by0.0020328419609201053674651... . The comparison
is recomputed from the original K0; the preceding identity gain is
not added a second time. It retains the same actual source and
surviving mass, independent original test labels, every infinite
tail, the complete signed numerator, and all eight source fallback
branches. Both complete terminal gaps remain positive. Unrestricted
Erdos #7 remains open; this is ordinary mathematics with exact
rational verification, not Lean verification or a sharpness claim.

## 1. A weighted event can be retained without assuming an affine cost

Fix one of the41 linear costs f and its fixed barrier C. It is
increasing and discretely convex, with a complete eventually affine
tail. Its selected source cost psi has increments at least those
of f by47(L2), with outside coefficient1. For an original zero-five
ternary layout b and first-positive-five layout c5, put

    v_l=f(b_l+1)-f(b_l), k_l=C-f(b_l), t_l=c5_l*v_l,
    vmin=f(2)-f(1), vmax=f(4)-f(3).

Since b_l is in{1,2,3},

    0<=vmin<=v_l<=vmax, 0<=t_l-v_l<=t_l<=k_l.          (WM2)

The independently labelled zero-seven test events5,15,45 are
I5,I15,I45. Convexity and the fixed barrier give both floors

    (C-f(A))_+<=k_l-v_l*(I5+I15+I45),
    (C-f(A)+v_l*I5)_+<=k_l-v_l*(I15+I45),            (WM3)

with nonnegative right sides. The second inequality follows from
f(A)>=f(b_l)+v_l*(I5+I15+I45). It does not identify f(A-I5)
with f(A)-v_l*I5.

Write Lambda for the actual raw35 source and mu for its surviving
marginal. Let F_J be the independent first-five slot of I5. Set

    Cap_v=(1/5)*integral v deta,
    L_v=Cap_v-integral_(F_J) v dmu.                  (WM4)

Profile47 retains the three selected source payments separately.
The marked one is Cap_v-integral_(F_J)v dLambda. If U is its old
fixed-layout full source envelope, then

    integral_raw f(A)
      <=U-[Cap_v-integral_(F_J)v dLambda]
                                      -(other two payments). (WM5)

The raw integral here is over the same full pre-mixed7 measure;
the displayed marked event depends only on the old coordinates.
For the deleted full357 measure, the second floor in(WM3) implies

    integral_deleted(C-f(A))
      <=integral[k-v*(I15+I45)]d(delta)
                                      -integral_(F_J)v d(delta),

where delta is its old-coordinate projection. Combine this with
(WM5) and the exact signed deficit identity. The other two event
payments go through the same old L3 argument, now with correction
t-v instead of t. This gives

    d_actual>=C*s-U+L_v-W_c(k,t-v)/5                 (WM6)

before the appropriate actual carrier averaging and layout
minimization. Every source payment is used once.

Missing selected test labels can be padded by arbitrary independent
test residues first. Since f is increasing, this only raises the
cost whose deficit is being bounded. It adds no forbidden deletion
and changes neither the actual source nor the carrier mixture.

## 2. Keep the shallow payment exactly and bound only the deep change

The true conditional cap of47/49 has selected terms

    A_c(k*n-t*eta/5)+(13/243)*max_l(k_l*d_l-t_l/5).

All its other terms are independent of t. On replacing t by t-v,
the shallow change, after the outside1/5, is exactly

    Psh_c(v)=[integral_(root c)v deta
                                +integral_(cell c)v deta]/25,

with empty carrier components contributing zero. Each selected
deep entry increases by v_l/5. Therefore

    0<=max_l(z_l+v_l/5)-max_l z_l<=vmax/5,
    [W_c(k,t-v)-W_c(k,t)]/5
                           <=Psh_c(v)+(13/6075)*vmax. (WM7)

The deep coefficient is the full sum of the selected ternary
depths3,4,5. The unselected depth>=6 tail is still1/486; positive5
cofactor terms and the entire seven tail are unchanged.

Let v3,v9 be the actual complete shallow virtual densities from89.
They depend only on ternary coordinates, use the same original
seven weights as pi, and include absent carriers. Averaging the
shallow payment gives the exact identity

    Psh(v)=sum_c pi_c*Psh_c(v)
                  =(1/5)*integral v*(v3+v9)deta.      (WM8)

Let M=eta tensor Haar5 and W=M-Lambda>=0. Suppose
1-v3-v9>=w>=0 pointwise. Since v is ternary measurable, the
same product calculation as89 cancels(WM8) against the actual
shallow virtual deletion. With x_J=W(F_J), it gives

    L_v-Psh(v)>=w*vmin*x_J+V5(v*I5)-vmax*omega,       (WM9)

after dropping the nonnegative other virtual deletions. Here
omega=(V-delta)(1), and V5 is the complete original cofactor5
virtual family. This is one actual error measure, not a separate
error allowance for each event.

## 3. A common bound for every independent original test

Use85's general packing hypotheses. Let H be the best first-five
slot, r=min_J x_J, m=Lambda(F_H), and G>0 its separation from
every other slot. Let E5 be the complete cofactor5 unused capacity.
The same actual mass residual satisfies

    E5>=r/5, E5+omega<=rho,
    q5<=(E5-r/5)/G,
    V5(v*I_H)=(1/5-q5)*integral_(F_H)v dLambda
             >=vmin*m/5-vmax*(m/G)*(E5-r/5).          (WM10)

For J!=H, use x_J>=r+G in(WM9) and discard V5. For J=H,
use(WM10) and bound the sum of E5-r/5 and omega once. If
c>=max(1,m/G), both cases give

    L_v-Psh(v)>=vmin*min(w*G,m/5)-vmax*c*rho.          (WM11)

Combining(WM6)--(WM11), then taking the better of the retained
and unchanged old bounds, proves the uniform weighted theorem

    d_actual>=m_old+[a_f-vmax*c*rho]_+,
    a_f=vmin*min(w*G,m/5)-(13/6075)*vmax.             (WM12)

Here m_old is the actual carrier average of the true globally
defined profile49 conditional function. Although v_l depends on
the original test layout, the right-side gain uses only vmin and
vmax, so it is uniform before minimizing over every layout and
averaging over pi. Different costs retain their own original
modulus5 tests; no residues or maximizing layouts are identified.

## 4. Use concentration and a fixed collection of22 costs

Let zeta=q(Z_K) be the same product-barycentric mass on71's two
K zero boxes. Fix

    delta_star=2/27, r_star=1/2500.

If zeta>=1-delta_star, the selected controlling carrier has weight
at least1-delta_star and consists of a disjoint root1 and root0
cell. As in89,

    w=1-(1+delta_star)/5=106/135.

The same concentration gives

    Delta<=3*delta_star/4=1/18,
    eta_star>=1/9-delta_star/18,
    h1>=1/3-delta_star/6.

For r<r_star these bounds satisfy the general hypotheses of85's
packing lemma, including the first-label and distinct-slot guards.
Its four gap entries give

    G>=Gstar=12271/911250,
    c=max(1,(1/9)/Gstar)=101250/12271,
    m/5>=1/50-r_star/5,
    min(w*Gstar,1/50-r_star/5)=650363/61509375.        (WM13)

The r_star cutoff uses the general packing argument; it is not
restricted to85's smaller illustrative cutoff1/12000.

For each cost i compute a_i by(WM12) with(WM13), and select
exactly the positive values. The fixed selected indices are

    4,5,6,9,11,13,14,15,20,21,22,
    25,27,29,30,31,34,35,37,38,39,40.

These22 indices depend only on the pinned cost inventory and the
displayed constants. The other19 linear costs, all five quadratic
costs, and the full square term keep their old inequalities.
No costs are selected according to the actual source or test.

Use exactly the old positive comparison weights beta_i:1 for R17,
P17 for R19, EXTRA5 for R5, and the complete complementary AP
tail coefficient for direction40. The exact sums are

    Bmark=sum_selected beta_i*a_i
      =161213733329143356587490859/37528335927295467378374250000
      =0.0042957868859804104923491...,

    Pmark=c*sum_selected beta_i*vmax_i
      =531765455625/77286341132
      =6.8804584074795246188806... .                 (WM14)

All inequalities share the same rho. Their penalties must be
added; they are not given separate budgets. The old signed mass
coefficient Acur from74 satisfies Acur>Pmark. Thus

    Acur*rho+sum_selected beta_i*[a_i-vmax_i*c*rho]_+
      >=Bmark+(Acur-Pmark)*rho>=Bmark.              (WM15)

This explicitly absorbs the combined charge for all22 tests once.

## 5. Complete global comparison from the original target

At the original K0, the same old separately concave expressions
give the signed lower bound

    Phi_K0_old>=B+A0*rho,
    B>=gamma_K*(1-zeta), A0>=Acur>0.

If zeta<1-delta_star, retain reserve gamma_K*delta_star. If
zeta>=1-delta_star but r>=r_star, the always-valid E5>=r/5
gives reserve at least Acur/12500. In the remaining case(WM15)
gives Bmark. The exact comparisons establish

    R=gamma_K*(2/27)
     =15240056495574031935365456355486859072608164346131
         /4382037533581480509635704696198176213230886000000000
     =0.0034778470925414895654567...
     <min(Acur/12500,Bmark).                        (WM16)

These cases cover the entire actual effective9 branch. They use
the old true functions for interpolation and apply the new cost
inequalities pointwise; no improved vertex table is asserted to
be concave.

Retain the positive complete denominator E of74/89, with
0<rho53*S<=E<=5/9. Set

    h=9*R/10, Knew=K0-h.

The new signed comparison is at least R-hE>=R/2>0, proving(WM1).
This calculation starts at K0. Direction40 appears once among
the22 selected costs, and89's preceding gain is not added again.

The exact checker verifies the positive-offset and signed-mass
branches at Knew, all eight complete fallback bounds, and both
complete-core gaps. The latter remain positive; the full terminal
comparison is not solved.

## 6. Verification and infinite tails

The [checker](../frontier/weighted_marker_global.py) checks each
of the41 cost and source increment sequences through the finite
prefix and into their complete affine tails. It checks all100
original layout pairs and five cells for each cost, the unchanged
barriers and weights, the coordinatewise deep-max bound, the22
fixed selections, their exact total gain and combined residual
penalty, and the complete global comparison. The pinned ordinary
source operators retain all unselected cofactor, source and AP
tails. No finite exponent truncation or label identification is
introduced by this calculation.

The general inequalities(WM3), (WM7) and(WM9)--(WM12) are proved
above; finite arithmetic does not replace their measure and
all-parameter quantifiers. The
[certificate](../certificates/source_norms/weighted_marker_global.json)
records every cost, every selection decision and the exact target.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/weighted_marker_global.py --check
```
