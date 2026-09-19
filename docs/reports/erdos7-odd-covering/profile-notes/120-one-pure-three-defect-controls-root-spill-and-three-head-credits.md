[Index](../marked_head_profile.md) · [Complete pure3 projection](119-the-complete-pure-three-family-has-one-projected-defect.md) · [Mean-head credit](109-the-mean-and-all-hinges-share-one-original-test.md) · [Finite source transport](116-signed-face-duals-transport-one-shared-finite-source.md) · [Selected deep-family payment](102-one-root-imbalance-charge-reduces-the-deep-capacity-penalty.md)

# One pure-three defect controls root spill and three head credits

The complete deep-pure3 virtual family can leave root0 away from the
K faces, but its actual unused capacity controls the mass that enters
root1. This gives a positive root0 five-coordinate defect with a complete
tail bound. It quantitatively transports three of109's five pure3
mean-head terms, using one shared measure rather than an independent
loss for every head event.

Let D=max_l d_l, R=max_(l>=2)d_l and assume the actual root gap
g=D-R>0. With119's complete defect E3 and pure5 survivor measure q,

    (V3deep restricted to root1)(1)<=R*E3/g,
    Xi0=q/90-(V3deep restricted to root0)^5>=0,
    Xi0(1)<=D*E3/g+(z-D)/90, z=q(1).              (RS1)

Moreover0<=Xi0<=q/90<=Haar5/90. These are ordinary measure inequalities
with exact rational checks, not Lean results. The forced27 cell1 terms
and109's extra deep-five credit require separate input; no new global
comparison is asserted here.

## 1. Charge the root1 spill to each actual original label

Use the actual source and all original forbidden labels(a,0,e),
a>=3,e>=1, with their independent residues. An absent label has empty
old-coordinate cylinder. Write J_(a,e) for that cylinder, L=3^-a and
u_e=6/(5*7^e), and define

    e_(a,e)=D*L-Lambda(J_(a,e))>=0.

As in119, the complete virtual measure and unused capacity are

    V3deep=sum_(a>=3,e>=1)u_e*1_(J_(a,e))*Lambda,
    E3=sum_(a>=3,e>=1)u_e*e_(a,e)
      =D/90-V3deep(1).                            (RS2)

The equality uses the entire sums1/18 and1/5. All summands are
nonnegative; finite partial sums increase to the displayed measures
and quantities.

Every nonempty cylinder belongs to one surviving ternary cell. If it
lies in root1, let m=Lambda(J). Its cap is m<=R*L. Therefore

    g*m=(D-R)*m<=R*(D*L-m)=R*e_(a,e).             (RS3)

Sum(RS3) only over those actual labels lying in root1 and use their
nonnegative defects as a subfamily of(RS2). This proves the first
inequality in(RS1). A label in the removed ternary root has zero
source mass and no spill. An absent label also has zero mass. Both
still contribute their full nonnegative capacity defect to E3, so
neither requires a special subtraction or a finite-depth convention.

The condition g>0 is explicit. In the broad slab Delta<=1/18,
99(TD5) supplies D>=25/36 and R<=5/9, hence g>=5/36. In that slab

    R/g<=4, D/g=1+R/g<=5.                         (RS4)

Using the actual ratio instead of these uniform bounds retains more
information. No assumption that all deep pure3 labels occupy cell1
is used.

## 2. A positive projection retains the same complete defect

Profile119 proved

    Xi=q/90-(V3deep)^5>=0,
    Xi(1)=E3+(z-D)/90.                            (RS5)

Let W=(V3deep restricted to root1)^5. There is no virtual source mass
in the removed root, so

    Xi0=Xi+W.                                    (RS6)

Both terms are positive. Combining(RS3)--(RS6) gives

    Xi0(1)<=E3+(z-D)/90+(R/g)*E3
           =(D/g)*E3+(z-D)/90.

Its original definition also gives Xi0<=q/90. Consequently, for every
five-measurable F,

    V3deep(root0 times F)
       >=q(F)/90-min(e0,Haar5(F)/90),
    e0=(D/g)*E3+(z-D)/90.                         (RS7)

This is a common measure statement, not separate independent error
variables for different F. For arbitrary original five cylinders F_b
of depth b>=b0, even with unrelated residues at different depths,

    sum_(b>=b0)Xi0(F_b)
       <=sum_(b>=b0)min(e0,5^-b/90).              (RS8)

The right side is an entire geometric-cap series. For e0=0 it is zero.
Otherwise let N>=b0 be the first integer with5^-N/90<=e0. Then it is

    (N-b0)*e0+5^-N/72.                           (RS9)

The implementation directly reuses66's exact min_geometric evaluator.
Haar domination is essential: a bare mass e0 with arbitrary atomic
support would not imply(RS8).

## 3. Three original mean-head indicators share Xi and W

Keep109's original layout(r3,c9,s5,r15,s15,c45,s45) and load B. Its
five nonunit indicators correspond to3,9,5,15,45. Set

    I=1_(r3=0), J=1_(r15=0),
    psi=I+1_(F_s5)+J*1_(F_s15),
    psi0=I+J*1_(F_s15).

Retain only the root0 part of the test3 and test15 indicators and
the entire test5 indicator. Discarding the nonnegative9 and45 terms
and any remaining root1 terms gives

    integral(B-1)dV3deep
      >=[I*z+q(F_s5)+J*q(F_s15)]/90
                              -integral psi dXi-integral psi0 dW. (HC1)

Indeed substitute V3deep^5=q/90-Xi for the test5 event and
V3deep|root0^5=q/90-Xi-W for the other two events. Linearity counts
overlapping original test events with their correct multiplicities.

The exact supremum bounds are

    M_Xi=I+1+J*1_(s5=s15), M_W=I+J.              (HC2)

When the two five slots differ, their indicators are disjoint, so
they do not require two copies of the Xi mass. Equations(RS3),(RS5)
and(HC1)--(HC2) yield the explicit nonnegative credit

    C3_partial(layout)=[A_layout
          -(M_Xi+M_W*R/g)*E3-M_Xi*(z-D)/90]_+,
    A_layout=[I*z+q(F_s5)+J*q(F_s15)]/90,
    integral(B-1)dV3deep>=C3_partial(layout).     (HC3)

The positive part is valid because the integral itself is nonnegative.
On either K face, E3=0 and z=D=3/4. Formula(HC3) recovers exactly

    I/120+q[s5]/90+J*q[s15]/90,                   (HC4)

the first, third and fourth pure3 terms of109(MH4). It does not
recover the1_(c9=1)/180 or1_(c45=1)*q[s45]/135 terms, which depend
on the additional forced27 geometry.

The q slot values in(HC3) can remain actual observations. Alternatively,
on116's source packing domain, with canonical slots(P,A,B,Q,H), valid
lower bounds are

    q(P)=0,
    q(A)>=1/5-a, q(B)>=1/5-b,
    q(Q)>=3/20+p, q(H)>=1/5-u,
    u=min(r/h,r1/h1,(r-r1)/h0).                  (HC5)

For A and B, the first alpha/beta source label and the complete
remaining tail1/20 supply the inequalities already used in88. The
complete pure5 deletion outside P has mass1/20-p, so its intersection
with Q is at most this amount. The H bound follows from its actual
root loss as in116(S5). Substituting any of these lower bounds in
A_layout preserves(HC3).

Presence of the full first pure5 source cylinder also forces
p<=1/20: its raw deletion mass1/5 is part of the total1/4-p. The
slot-lower interface checks this necessary actual-source constraint.

## 4. Insert the credit with the existing single union-error payment

Profile116's retained density w^q contains the virtual shallow3/9
families and the correctly located cofactor5/15 families. Their
original modulus labels are disjoint from the deep pure3 family.
With epsilon=V-delta>=0, epsilon(1)=omega, one has the measure bound

    mu<=w^q*Lambda-V3deep+epsilon.                (HC6)

This inequality does not assert mu<=w^q*Lambda off the face. For a
nonnegative combination of the bounded finite old heads, retain the
V3deep subtraction only for its coefficient a1 times(B-1), and discard
the other nonnegative deep-family contributions. Thus116's bound
improves by a1*C3_partial, with its existing single M_a*omega payment:

    finite_upper+complete_remainder+M_a*omega
                                      -a1*C3_partial.          (HC7)

There is no second omega charge for invoking(HC3). Conversely no
argument here permits omitting116's first union-error payment.
The complete remainder and the constant term a0*S remain exactly the
external inputs specified in116. If additional credit from forced27
or deep-five families is proved, it must be combined with(HC3) on
the same original test and against the same error measure.

## 5. The selected E_D is inside E3

For the selected original depths3<=a<=k used by99/102, with k=5 or6,

    E_D=sum_(3<=a<=k,e>=1)u_e*e_(a,e),
    E_tail=sum_(a>k,e>=1)u_e*e_(a,e),
    E3=E_D+E_tail.                               (AC1)

Thus0<=E_D<=E3. The distinct cofactor families5,15 and deep3 give

    E5+E15+E3+omega<=rho.                         (AC2)

They do not give(AC2) with an additional E_D on the left. If one
consumer simultaneously pays kappa*E_D from102 and lambda*E3 here,
its exact combined charge is

    (kappa+lambda)*E_D+lambda*E_tail,             (AC3)

which is at most(kappa+lambda)*E3 for nonnegative prices. With both
k=5 and k=6 consumers, use the common depth partition3..5,6,>6
and add the applicable prices in each part. This keeps every original
label's capacity defect in exactly one underlying budget coordinate.

In particular117's wrong-slot budget can be retained as

    E3+omega+G5*q5+G15*q15<=rho-(r+r1)/5,         (AC4)

with its proved gap prices. All terms in(HC3),119's tail bound and102's
selected payment must be optimized against this same allocation.
The positive-part credit and119's nonlinear complete error do not
automatically preserve116's finite q-polygon convexity.

## 6. Independent check of119's concentration interface

Suppose qK>=1-sigma, 0<=sigma<1/2, and select the canonical orientation
using106. Then deficit0>=(1-sigma)/2, pi_(1,1)>=1-sigma,
alpha0<=sigma/4 and beta0+beta1<=sigma/4.

Writing D0=deficit0 and Drest=sum_(l!=0)deficit_l gives

    h=(5-D0-Drest)/9<=1/2+sigma/18,
    c5=sum_l eta_l*(1-t_l/5)-1/90
       <=(5-D0-Drest)/9
                         -(1-sigma)*(4-Drest)/45-1/90
       <=2/5+13*sigma/90.                        (SC1)

The Drest coefficient is-(4+sigma)/45, so its maximum is at zero;
the D0 coefficient is negative, so substitute its lower bound.
Also D is at least the larger of the two root0 availabilities, hence

    z-D<=alpha0+min(beta0,beta1)<=3*sigma/8,
    (z-D)/90<=sigma/240.                         (SC2)

These independently verify119's final three bounds. The earlier
quadratic reference bound remains valid, because

    [2/5+sigma/6-sigma²/45]-[2/5+13*sigma/90]
      =sigma*(1-sigma)/45>=0.                    (SC3)

The stronger shared-deficit bound(SC1) is the interface used by119.
The other orientation follows by the full cell0/cell1 exchange.

## Reproduction and scope

Run

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/pure_three_root_spill.py --check

The program independently enumerates the old35 source at height3
for six original cofactor configurations: cell0,cell1,root1,removed
root,mixed and absent. A seventh finite family uses original depths
3<=a<=8 and1<=e<=6 in cell1; its larger-depth cylinders are evaluated
using the exact product source fiber checked in the height3 mask.
The remaining original exponent labels are absent, and their complete
capacity remains in E3. The seventh family has94 strictly positive
three-indicator credits among100 original head choices.

The certificate verifies the positive projected measures, root spill,
complete descendant error,700 original three-indicator head inequalities,
both selected-depth partitions and100 exact face credit identities.
These finite cases check the implementation and explicit constructions;
the ordinary proof above establishes the all-depth assertions.

The helper exports spill_bounds, partial_head_credit and
canonical_slot_lowers. It pins119's final projection interface and
reuses66's complete geometric series. Forced27 localization, the extra
deep-five mean credit and a resulting whole-neighborhood numerical
comparison are outside this result.
