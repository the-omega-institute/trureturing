[Index](../marked_head_profile.md) · [Source measures](31-one-original-zero-five-layout-across-both-actual-measures.md) · [Retained and removed events](33-retained-and-removed-original-events-control-convex-costs.md)

# Original 15 and 45 test events sharpen the uniform357 square bound

For every finite family of distinct nonunit congruence moduli supported
on {3,5,7}, with arbitrary independent original forbidden residues, let
S be its complete actual survivor set. The established survival theorem
makes S nonempty. For every complete original test

    L(x)=sum_(d divides Q) 1_(x=b_d mod d),
    Q=3^H 5^K 7^E,

including its unit term, the same uniform probability on S satisfies

    E_(Unif(S)) L^2 <= G,
    G=102715/2916=35.22462277091907... .                (TF1)

Here H,K,E are arbitrary finite nonnegative integers, Q is any common
period of the forbidden moduli, S is taken in Z/QZ, and every test residue b_d is chosen
independently at its original label. There is no compatibility assumption
between residues at different divisors. The bound also applies to partial
tests by adding their missing nonnegative terms. Missing original forbidden
classes remain missing; completing a test never inserts a forbidden class.
If a comparison requires additional coordinates, lift to a larger finite
period, leaving the actual probability and forbidden family unchanged,
and dominate the original test by its complete extension.

The proof retains the original unit5,15 and45 test events in the same
source and deletion calculation. It improves the preceding source bound
1730443/48600 by55579/145800=0.3812002743484225... . All exponent tails
are summed completely. The result is an ordinary mathematical inequality
with exact rational checks, not a Lean-kernel theorem or a solution of
unrestricted Erdos #7.

The proof uses the established actual-measure density and arbitrary-prefix
bounds in [profile31](31-one-original-zero-five-layout-across-both-actual-measures.md),
the complete current7 source/deletion comparison and missing-class branches
in [profile32](32-unequal-source-norms-sharpen-the-uniform357-input.md),
the same-event retained/removed accounting in [profile33](33-retained-and-removed-original-events-control-convex-costs.md),
and the actual pure3 distance inequality in [profile34](34-original-layout-distance-forces-a-jensen-loss.md).
The effective original9 branch is treated below; the missing-class bounds
at the end cover the other source branches.

## Actual source measures and original tests

Use the raw actual35 measure lambda35 on the original old product and the
raw pure3 measure eta. Their original five-cell data are d_l,n_l,eta_l,s,
with lambda35(cell_l)=n_l and the actual marginal density at most d_l.
The five cells have root labels (0,0,1,1,1). Every original exponent and
every label keeps its own residue. All following comparison sums include
the complete infinite geometric tails and thus bound every finite height.

Fix one original zero7 complete35 test A0. Write B0 for its zero5 ternary
block and B1 for its first-positive5 ternary block after removing only the
five-coordinate factors. Their original shallow ternary baselines are

    b_l=1+1_(root(l)=r0)+1_(l=j0),
    c_l=1+1_(root(l)=r1)+1_(l=j1).

The choices r1 and j1 are respectively the original ternary parts of labels
15 and45. They need not agree with r0,j0, or even be incident with each other.
Complete or dominate missing/killed test coordinates as in profile34; this
increases the complete test on the fixed actual survivor law. It changes no
forbidden residue or probability. The ten b and ten c choices are retained
until the source and deletion expressions have been added.

The original15 and45 indicators remain attached to this same c in both
the source norm and the weighted deletion floor. The original unit5
retained/removed budget and the N5=2 distance deduction enter only once.

## The first-positive5 block through the entire source comparison

Define

    M_c=sum_l eta_l*c_l^2+max_l(c_l+1)/9,
    M=max_c M_c,
    A_b=sum_l n_l*b_l^2+(1/4)sum_l eta_l*b_l^2
          +max_l(d_l+1/4)(b_l+1)/9.

The arbitrary-original-prefix square bound proves integral_eta B1^2<=M_c.
The complete ternary identity used in A_b is

    sum_(a>=3)3^-a[2(b+a-3)+1]=(b+1)/9.

The raw pure5 comparison has p_n=4/5^n for n>=2. On its n-strip retain the
same original B0,B1,...,B_(n-1). Square Jensen gives

    (sum_(i=0..n-1)B_i)^2 <= n sum_i B_i^2.

At n=2 use its exact saving (B0-B1)^2. The full coefficients are

    sum_(n>=2)p_n(n-1)=1/4,
    sum_(n>=2)p_n*n=9/20,
    sum_(n>=3)p_n*n(n-2)=7/40,
    p_2=4/25.

Profile34's actual pure3 distance lower bound is

    d_eta(b,c)=sum_l eta_l(b_l-c_l)^2
       -[max(0,max_l(b_l-c_l))^2+max(0,max_l(c_l-b_l))^2]/18.

Combining the actual B0 square and its pure square before the deep-prefix
allocation, and bounding all other positive5 blocks independently by M,
gives the retained source expression

    U_bc=A_b+(9/20)M_c+(7/40)M-(4/25)d_eta(b,c).       (T1)

For comparison, the published selected source is

    max_c[A_b+(8/25)M_c+(61/200)M-(4/25)d_eta(b,c)].

Thus (T1) only keeps B1's baseline in the remaining 13/100 of its source
coefficient. This retention alone can have zero gain at the old controlling
vertices. Its purpose here is to couple that same c to deletion.

## Three actual events, without identifying their five residues

For t=0,1,2 let I_t be the actual test event at original labels5,15,45:

    I_0=J_0,
    I_1={old ternary root r1} intersect J_1,
    I_2={old ternary cell j1} intersect J_2.

Each J_t is its own original residue modulo5. Let D_t denote the respective
old ternary carrier (the whole carrier, root r1, or cell j1), and let
 h_t=Haar(P5 intersect J_t)<=1/5. No equality between the J_t is assumed.
On cell l the number of possible active selected indicators is at most c_l.
Put v_l=2b_l+1 and k_l=C-b_l^2.

Write A0=B0+V. Since V is a nonnegative integer and V>=sum_t 1_(I_t),

    A0^2-B0^2=2B0 V+V^2 >= v_l sum_t 1_(I_t).        (T2)

Define the actual enlargement-loss terms

    K_t=integral_(eta restricted to D_t) v,
    R_t=h_t K_t-integral_lambda35 v 1_(I_t)>=0.

Enlarging only the positive5 increment from lambda35 to the actual pure
product overcounts by at least sum_t R_t, by(T2). In the nested-cap upper
comparison, enlarging each of these three individual intervals from h_t
to1/5 increases the integrand by at least v_l on its active ternary carrier.
This follows from the square increment (B+1)^2-B^2>=2b_l+1. It applies
successively even if the selected intervals exchange order or overlap.
Consequently the same source chain yielding(T1) gives

    integral_lambda35 A0^2
      <=U_bc-sum_t[(1/5-h_t)K_t+R_t].                (T3)

The enlargement loss and cap-shrink loss are different steps. The
N5=2 Jensen loss is applied only after returning all caps to1/5, so it is
not subtracted from an independently maximized deletion term.

For C>=30, since b_l,c_l<=3,

    C >= b_l^2+v_l*c_l.

Therefore the right-hand side in the following additive floor is
nonnegative, even when all three actual events occur:

    (C-A0^2)_+ <= k_l-v_l sum_t 1_(I_t).             (T4)

Indeed A0>=b_l+sum_t1_(I_t), and the square of the latter is at least
b_l^2+v_l sum_t1_(I_t). No cross term is needed or counted.

## The same source budget pays the three floors together

At each positive7 depth e, retain the actual six pure3 cofactor cylinders
E_(a,e), a=1,...,6. For each of the three selected events put

    K_t(E)=integral_(eta restricted to D_t intersect E) v,
    T_t(E)=integral_(lambda35 restricted to E) v 1_(I_t),
    R_t(E)=h_t K_t(E)-T_t(E)>=0.

The original positive7 coefficients tau_e satisfy sum_e tau_e<=1/5.
The six actual cylinders have pointwise multiplicity at most6. Hence,
separately for each t,

    sum_e tau_e sum_a R_t(E_(a,e)) <= (6/5)R_t,
    sum_e tau_e sum_a K_t(E_(a,e)) <= (6/5)K_t.       (T5)

The existing SD5 source coefficient of this SAME A0 is6/5. Multiply(T3)
by6/5 and add the deletion estimates(T4), retaining all three sums.
The first inequality(T5) pays every lost retained-event intersection.
The coefficient of each h_t is nonnegative by the second inequality(T5),
so the upper value occurs at h_t=1/5. After this combination the selected
cylinder contribution is

    integral_E k d lambda35 -(1/5)sum_t K_t(E).

On cell l, sum_t1_(D_t)=c_l. This is the new corrected weight; the unit5
part is contained in it and is not deducted a second time.

## Explicit all-height signed cofactor expression

Let R(x)=max(sum_(l<2)x_l,sum_(l>=2)x_l). Put

    s_l=k_l*n_l-v_l*c_l*eta_l/5,
    q_l=k_l*d_l-v_l*c_l/5,
    w_l=9*eta_l.

For C>=30 and the inherited domain d_l>=1/4, q_l>=21/20>0.
Also sum_l s_l>=21s-(21/5)sum_l eta_l>=21/4-7/3>0,
using s>=1/4 and sum_l eta_l<=5/9. Empty root/cell alternatives are thus
covered by their maximum, and signed deep cylinder caps keep their direction.
The resulting complete cofactor expression is

    W_bc(C)=R(s)+max_l s_l
       +(40/729)max_l q_l+(1/1458)max_l k_l*d_l
       +[sum_l k_l*w_l+R(k*w)+max_l k_l*w_l]/36
       +max_l k_l/72.                               (T6)

The selected deep sum40/729 is over original depths3,...,6;1/1458 is the
full a>=7 tail. The four positive5 cofactor terms are unchanged. As in
KRM, W_bc is a component of the joint expression, not a standalone upper
bound on actual deletion.

Let U_global=max_b A_b+(5/8)M, the unchanged raw35 square upper bound
for the independent positive7 original tests. The existing SD5 comparison
and(T3)--(T6) give the following inequality. Here M35x7 is the normalized
actual uniform35 survivor probability times the normalized actual pure7
survivor probability, and B is the actual mixed7 forbidden union:

    s E_M35x7[(L^2-C)1_(B^c)]
       <=(6/5)U_bc+(7/15)U_global+W_bc(C)/5-C*s.     (T7)

Thus nonpositive(T7), uniformly over b,c and the original parameter
domain, bounds the complete actual uniform357 square by C. Actual
survival positivity is the existing CM2 input. No new probability law,
product assumption after deletion, current7 nesting, or forced agreement
of independent test residues is introduced.

For fixed C,b,c the right side before -Cs is separately convex in the
five inherited parameter groups. M_c and d_eta(b,c) are affine in eta;
the remaining original deep allocations and cylinder terms are maxima
of separately affine functions with nonnegative prefactors. Consequently
the margin is separately concave. The full1296 parameter-vertex check
for every b,c therefore extends to the complete continuous domain.
The inherited missing3 and missing/ineffective9 bounds are5273/258 and
14543/438; the fixed C must dominate both. This is the same all-height
extension as the source modules, not a finite residue enumeration.

## Complete-domain verification and the remaining source branches

Set C=G in(T7). Exact rational evaluation checks all1296 vertices of the
five inherited parameter groups, all10 original zero5 layouts b and all10
original first-positive5 layouts c:129600 margins in total. Every margin
is nonnegative. The minimum is0, attained at24 parameter/layout tuples.
A representative is vertex402 with b=c=layout8; its active margin is

    (3/20)C-20543/3888,

which vanishes at C=102715/2916. This equality concerns the bounding
formula, not a claim that an actual congruence family attains G.

The source expression used for comparison is also matched exactly to the
preceding canonical selected-source formula at all1296*10=12960
parameter/b choices. This checks its normalization, coefficient6/5,
independent positive7 coefficient7/15, and the already retained N5=2
source deduction. The129600 inequalities then check the newly coupled
formula itself. Their role is to certify the finite vertex arithmetic;
separate concavity, proved above, supplies the full continuous-domain
conclusion. They are not an enumeration of bounded-height families.

If modulus3 is absent, the inherited bound is5273/258. If modulus3 is
present but9 is absent or ineffective, it is14543/438. Both are strictly
below102715/2916. Missing5/7 classes, partial inventories and all finite
heights are included by the complete cap sums and the unchanged source
parameter domain. Thus every branch satisfies(TF1).

The same pure7 law is used before the sole final conditioning on the
actual mixed7 survivor event. Positivity of that event is the existing
survival input. No weighted AP probability is substituted for this
uniform357 source, no original residues are reselected on sampled rows,
and no source or retained-event loss is spent twice. Propagating G to
later AP costs is a separate application on those laws and does not follow
by subtracting this source improvement from a later numerical bound.

## Propagation on the same actual AP(4,5) law

Use the actual AP11/T4 and AP13/T5 construction from
[profile35](35-ap45-layout-costs-and-complete-core-tails.md), followed by
its one final conditioning. The later17 and19 original tests remain
independent, and the19 input remains the physical probability nu13 K17.
Only the uniform357 square input changes. The five exceptional quadratic
norms and all41 linear norms keep their previously certified values.

Let G_old=1730443/48600 and g=G-G_old=-55579/145800. The complete
exceptional-tuple complement in the quadratic comparison is

    a_out=1600217/12882870.

The new quadratic cost is therefore

    H16_new=H16_old+a_out*g
           =6628250743995950539/99650640727638000.       (TF2)

H41 remains the complete linear cost from profile35. This is a change
inside the same full original-label comparison, not a subtraction of g
from a later bound. Recompute the independent auxiliary product N11*N13
with caps5/3 and12/7. Its complete second moment is1403/630. Write p_n
for its probabilities at n<9 and q0,q2 for its remaining mass and second
moment. The coefficient of D in the T81 numerator is

    B81(G)=G*q2-81*q0+sum_(n=7,8) p_n*n^2*(G-1).      (TF3)

All n<9 terms outside7,8 keep the previous actual357 square-hinge
formula. Thus both the infinite product tail and the two finite uniform
cap slots change with G. The positive survival denominator is unchanged:

    Delta=(919/924)D-B4/6-(4/33)B5-B_(5/2)/22.

At every parameter point the new consumer bounds are

    Gamma13 <=16+D*H16_new/Delta,
    J <=C0+D*((2371/2880)*H16_new+H41)/Delta.

The T81 bound is its complete new numerator divided by Delta. Exact
reconstruction over all1296 vertices, followed by the separately concave
margin argument from profile35, gives

    Gamma13 <=1815512269426569043079/11974427321722572564
             =151.6157909391695...,
    T13(81) <=51915922153739431127176510521019232999/
              538907998919806206156995074612316250
             =96.3354083773118...,
    J <=3810473925191689060079929550012316476553734981/
         8747916209798826239784056763989118368928000
       =435.5864681149384... .                       (TF4)

All three continuous-extension coefficients are positive. The six J
controllers remain398,410,422,616,628,640; the four T81 controllers are
386,388,590,592. Their extrema are computed separately. All eight other
source branches are reconstructed with the new G and the same actual
AP thresholds. The uniform survival lower bound remains
15447272417/31495117500.

The complete finite-core calculation retains the already proved source
constants3849/106 and432/53 where they bound both full and retained source
families, and uses the new Gamma13, T81 and the unchanged survival lower
bound at the AP input. Those older source constants are valid upper
bounds, not new values silently inferred from TF1. With the new later
input, all physical/killed-kernel and ordered-pair test tails are
recomputed. For box20 and current heights8,8 the exact sufficient
allowance is306.66399828212104..., with the safe bound306.663998.
The smaller retained box with current heights6,6 has safe bound306.436968.
The remaining gap to the larger exact allowance is128.92246983281734... .
The negative-Q criterion, arbitrary later-prime continuation and
unrestricted Erdos #7 remain open.

## Reproduction and verification scope

Run from the repository root:

```sh
python3 -B docs/reports/erdos7-odd-covering/frontier/verify_retained_five_tests.py --check
```

The [checker](../frontier/verify_retained_five_tests.py) rebuilds the
129600 source inequalities,12960 predecessor-source identities,1296
AP consumers,eight missing-class branches and both complete core-error
calculations. The [certificate](../certificates/source_norms/retained_five_tests.json)
records their exact extrema, full margin digest, complete-tail coefficients
and current result. Default and check modes do not write; only explicit
write mode regenerates this certificate. Source hashes bind the declared
predecessor artifacts and current calculation. Checking those hashes is
not replaying every ancestral verification program.

The finite arithmetic supports the ordinary actual-event, full-tail and
continuous-extension arguments above. It is not a Lean proof or a check
of every finite congruence family by enumeration.
