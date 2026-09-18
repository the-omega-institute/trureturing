[Index](../marked_head_profile.md) · [Whole face mean](109-the-mean-and-all-hinges-share-one-original-test.md) · [Finite source transport](116-signed-face-duals-transport-one-shared-finite-source.md) · [Root spill](120-one-pure-three-defect-controls-root-spill-and-three-head-credits.md) · [Quantitative27](121-the-original-forced27-exclusion-has-a-quantitative-defect.md) · [Deep five](122-two-complete-deep-five-families-transport-the-mean-credit.md)

# One original head transports the whole deep mean credit

All of109's additional mean correction has an explicit off-face
replacement, throughout121's actual concentrated domain and the source
packing domain whenever116's finite source operator is used. The
replacement keeps one original head and one common capacity budget.
For the27 family, combining the head indicators before bounding the
positive projection defect is stronger than separately adding120 and121.
Retaining the actual head on the wrong carriers strengthens it again.

The result transports a bounded mean correction. Complete omitted tails
remain explicit inputs to116; neither the corrected finite operator nor
its exact checks constitute a new global K comparison. All exponent
families used in this correction are complete. No Lean result is claimed.

## 1. One actual source and one original head

Take121's canonical orientation with0<=sigma<=2/27 and qK>=1-sigma.
Write

    D=max_l d_l, R=max_(l>=2)d_l, t=R/(D-R),
    z=q(1), g27=1/135-sigma/72, C=D/(27*g27).

These D and R are availability densities, not surviving total masses.
The concentrated source bounds give

    D>=3/4-sigma/2, R<=1/2+sigma/2,
    D-R>=1/4-sigma>=27*g27>0,
    C>=1+t.                                      (JM1)

The last inequality follows by multiplying by the positive denominators.
The middle one uses1/20-5*sigma/8>=1/270 on the stated interval.
Let eta have root masses h0<h1 and put R5=h1/(h1-h0), as in122.

Keep the same original head throughout:

    layout=(r3,c9,s5,r15,s15,c45,s45),
    B-1=I_test3+I_test9+I_test5+I_test15+I_test45.

Its five slots are the actual first-five partition, not independent
probability laws. For j in these slots define

    I=1_(r3=0), J=1_(r15=0),
    c=1_(c9=1), K=1_(c45=1),
    g(j)=I+1_(j=s5)+J*1_(j=s15),
    k(j)=c+K*1_(j=s45), f(j)=g(j)+k(j).

Define integer suprema on this same partition:

    Mxi=max g, M27=max k, M=max f,
    N0=max_j [k(j)-1_(c9=0)-1_(c45=0,j=s45)]_+,
    N1=max_j [2I-1+(2J-1)*1_(j=s15)+k(j)]_+.

The two complete pure3 prices are

    Lge4=Mxi+I*(1+J)*t,
    L27=M+max(N0*(C-1),N1*t).                    (JM2)

Every quantity is attached to the original head. In particular a change
of s5,s15 or s45 changes the common suprema, not three independently
maximized terms.

## 2. Project each original27 label before paying its error

For an original27*7^e label let lambda be the five-coordinate projection
of its actual old-source restriction, with lambda=0 when absent. Put

    L=1/27, d=D*L-lambda(1),
    nu=L*q-lambda>=0,
    nu(1)=d+(z-D)*L.                              (JM3)

Positivity follows from119's labelwise product cap. This is a statement
about the actual forbidden label, even when a later test uses a different
residue. The nominal reference for its whole pure3 head is L*q(f).

For a present carrier in cell1, its actual head is exactly f, so reference
minus actual contribution equals nu(f). On the wrong surviving cell0,
the actual head also includes its own test9/test45 indicators. The loss is

    nu(f)+lambda(k-1_(c9=0)-1_(c45=0)*1_(j=s45)).

It is at most M*nu(1)+N0*lambda(1). By121 the wrong cell loses at least
g27 of its nominal raw capacity. Therefore

    lambda(1)<=[D/(27*g27)-1]*d=(C-1)*d.

On root1, retain the actual test3 and test15 contributions
(1-I)+(1-J)*1_(j=s15), as well as test5. Discarding only the remaining
nonnegative actual test9/test45 terms bounds the loss by

    nu(f)+lambda(2I-1+(2J-1)*1_(j=s15)+k),

hence by M*nu(1)+N1*lambda(1). The root gap from120 gives
lambda(1)<=t*d. Removed roots or mod9 cells have zero source mass.
For them and absent labels the loss is simply nu(f).

Thus every original27 label has loss at most

    L27*d+M*(z-D)/27.

Multiply by its original u_e=6/(5*7^e) and sum all e>=1. The full
sum is1/5, including the nominal capacity for absent labels. The
complete27 head contribution is at least

    q(f)/135-L27*E27-M*(z-D)/135.                 (JM4)

The reference q(f)/135 records the head on the ideal cell1 measure;
no actual wrong carrier is relabeled or replaced in the proof.

## 3. Keep the actual root1 head at every deeper pure3 depth

For a>=4 use the same labelwise projection with L=3^-a and nominal
head g. On root0 its actual head is at least g. On root1 the discarded
cell indicators are nonnegative, and the reference minus the retained
actual head is

    2I-1+(2J-1)*1_(j=s15).

Its positive supremum is I*(1+J). In particular, when I=0 and J=1,
the actual root1 test3 indicator already pays for the missing root0
15 indicator. Charging both root mismatches independently would lose
this cancellation.

The same root-spill inequality proves the whole a>=4 contribution is
at least

    q(g)/270-Lge4*Ege4-Mxi*(z-D)/270.             (JM5)

Here1/270=sum_(a>=4,e>=1)3^-a*u_e. Together with(JM4),
q(g)/135+q(g)/270=q(g)/90, exactly the three-indicator reference of120.
No later ternary or seven exponent is dropped. E3=E27+Ege4.

## 4. Add the distinct complete deep-five families

For the same head use122's quantities

    A5=[(1+r3)*h_r3+(1+ROOT(c9))*eta_c9]/100,
    M5=1+1_(ROOT(c9)=r3),
    M15=1_(r3=1)+1_(ROOT(c9)=1).

Their combined virtual head contribution is at least

    A5-M5*E5d-M15*R5*E15d.                        (JM6)

These two families have original labels5^b*7^e and3*5^b*7^e,
b>=2,e>=1. They are disjoint from both pure3 depth groups and the
shallow families retained in116's density. Define

    A3=[I*z+q(s5)+J*q(s15)]/90,
    A27=[c*z+K*q(s45)]/135,
    A=A3+A27+A5,
    X=(Mxi/270+M/135)*(z-D).

Then the whole additional mean contribution is at least

    Cminus=A-X-L27*E27-Lge4*Ege4
                       -M5*E5d-M15*R5*E15d.       (JM7)

It is also at least max(Cminus,0). For the finite convex optimization
below we retain the affine lower bound itself. At sigma=rho=0 all
these defects and z-D vanish; A is precisely109's C3+C5, on the entire
actual beta face. Relabeling both source and test coordinates by the
cell0/cell1 exchange proves the other orientation.

## 5. Quantified comparison with the separate interfaces

The original120+121 sum would use

    L3_old=Mxi+(I+J)*t,
    L27_old=L3_old+M27*C,
    Xold=(Mxi/90+M27/135)*(z-D).

A first joint27 price that discards the extra actual indicators is

    L27_joint=M+max(M27*(C-1),N*t),
    N=max_j [I+J*1_(j=s15)+k(j)].

Since N0<=M27, N1<=N and I*(1+J)<=I+J,

    Lge4<=L3_old, L27<=L27_joint.

Also M<=Mxi+M27, N<=I+J+M27 and C>=1+t from(JM1). Bound the two
branches of L27_joint separately to obtain

    L27_joint<=L27_old,
    Xold-X=(Mxi+M27-M)*(z-D)/135>=0.              (JM8)

These inequalities hold throughout the actual domain, not just at the
numeric checks. At the face ratios C=15/4,t=2, among all12500 heads:
5900 have a strictly smaller full27 price,3125 have a smaller deeper3
price and1800 have a smaller source-discrepancy coefficient. The maximum
27-price saving is23/4. For example head(1,0,0,0,0,1,1) changes31/4
to2. These are coefficient improvements, not changes in global K.

## 6. One residual pays the finite corrected head

The complete capacity partition is

    E5sh+E15sh+E27+Ege4+E5d+E15d+omega<=rho.

Where117's packing guards hold, the same actual wrong-slot weights give

    E27+Ege4+E5d+E15d+omega<=e(q5,q15),
    e(q5,q15)=rho-(r+r1)/5-G5*q5-G15*q15.          (JM9)

There is one omega, and no extra E3 alongside its two components. Let
116's nonnegative hinge coefficients be a_t, with transfer coefficient
Ma=sum_t a_t*max(6+k_t-t,0), so Ma>=5*a1. Define

    Lb=max(Ma,a1*L27,a1*Lge4,a1*M5,a1*M15*R5).

Multiplying(JM7) by a1 and using(JM9), all capacity and union-error
penalties together are at most Lb*e. Thus116's complete branch obeys

    integral_mu f(A_test)
      <=a0*S+C_b(theta,q)+R_b-a1*A+a1*X+Lb*e.    (JM10)

R_b must be a separately proved upper for that branch's entire omitted
old and positive-seven remainder. The finite head bound C_b retains
one original test, or its own signed face-dual upper. Formula(JM10)
does not import109's saturated tail constants off face.

On sigma<=2/27, R5<=160/77, M5<=2 and M15<=2. Therefore the two deep5
prices satisfy a1*M5<=Ma and a1*M15*R5<Ma whenever a1>0. Restoring
this part of the mean credit does not increase the existing residual
coefficient. The pure3 prices still have to be retained in Lb.

For fixed actual source and fixed separately supplied tail upper, A,X
and Lb depend on the same head but not on q5,q15. The last term is affine
in q. Since116's C_b is convex in q, the corrected branch and its maximum
over heads are convex. Nonnegative sums across costs remain convex and
can use the vertices of one shared polygon. This conclusion excludes
nonlinear complete-tail errors;115's and123's interior counterexamples
remain applicable if those errors are inserted into the objective.

If a branch's own face slack is used, its face reference must include
-a1*A_face. The exact correction increment is a1*(A_face-A+X), together
with Lb*e and the same branch's finite-source and tail increments. The
constant term uses actual S, as required by116.

## Exact verification and scope

The [helper](../frontier/joint_deep_mean_transport.py) exposes mean_data,
mean_credit and joint_residual_price. It recovers109's exact correction
on all12500 original heads by directly invoking its existing reference
formula. Three complete12500-head inventories compare the joint and
separate prices at sigma=0,1/27,2/27.

Three genuine height5 original-label configurations independently test
the full virtual credit on all12500 heads each. They include correct
carriers, a wrong cell0 original27 label, a root1 original27 label, an
absent deeper3 label and a wrong-root deep15 label. All omitted depths
remain in their complete defects. Each configuration yields strictly
positive transported credits; the certificate records their counts and
minimum positive values. Each actual family also includes pure7 labels
with residue6*7^(e-1), and shallow3/9 labels with old carriers root1/cell1
for1<=e<=5; their complete virtual weights give the stated carrier pi
and hence the actual qK. Mixed-seven residues may all be0. The shallow
families are excluded from this additional credit. Absent shallow depths
occupy the empty-carrier weight7^-5 in pi; all missing deep-family
capacities remain in the four defects. The check computes virtual deletion,
not an actual seven union or a value for omega. These finite experiments check the concrete
interface, while the preceding positive-measure proof covers arbitrary
original heights and residues.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/joint_deep_mean_transport.py --check
```

The missing task is the full off-face tail and numerical comparison
consumer. This result closes the additional mean-credit input, not that
remaining task or unrestricted Erdős #7.
