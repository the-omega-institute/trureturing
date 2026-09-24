[Index](../../marked_head_profile.md) · [Actual finite families](../001-064/48-actual-source-compatibility-excludes-a-relaxed-mass-endpoint.md) · [Same-head original costs](109-the-mean-and-all-hinges-share-one-original-test.md) · [Finite source operator](116-signed-face-duals-transport-one-shared-finite-source.md) · [Whole mean transport](124-one-original-head-transports-the-whole-deep-mean-credit.md) · [Complete omitted tails](125-the-complete-off-face-omitted-tails-recover-every-face-constant.md)

# A complete off-face original cost has no unspecified tail

The finite source bound, full additional mean credit and all omitted
exponent tails now form one executable actual-source cost bound. Its
first numerical instance is the original AP cost1, R17 with exponent
tuple(0,1), from109. It recovers the published face maximum exactly and
bounds the same complete cost at two genuine finite398 source families.

| Actual source data | Complete cost upper |
| --- | ---: |
| Saturated K face | 1.558338399818915230844287075... |
| Finite398 family, height5 | 1.567846241014622198766261748... |
| Finite398 family, height8 | 1.558820934436428831680697598... |

Each row maximizes over all12500 original heads and all10 independent
positive-seven projections. The cost's entire affine load tail and
every original exponent tail are retained. These are upper bounds for
all independent original tests at the stated source data; they are not
values attained by the actual family. The finite rows do not establish
a uniform bound at other sources, or a new global K. The unrestricted
covering question remains open. No Lean verification is claimed.

## 1. A complete conditional theorem

Fix actual source and carrier data satisfying116's source-packing domain
and124's canonical concentration qK>=1-sigma,0<=sigma<=2/27. Keep the
same actual wrong-slot weights q5,q15, survivor mass S, and capacity
vector

    E5,E15,E27,Ege4,E5d,E15d,omega,
    E3=E27+Ege4,
    E5+E15+E3+E5d+E15d+omega<=rho.

All entries refer to the actual family. A feasible relaxed parameter
vector alone does not supply such a family.

Let an original nonnegative integer-load cost have the already verified
complete expansion

    f(v)=a0+sum_(t=1..8)a_t*(v-t)_+, a_t>=0.

Use116's finite branch C_b(theta,q), prefix lengths k_t=min(t-1,4),
and bounded transfer price Ma=sum_t a_t*max(6+k_t-t,0). For each
original head b, use124's lower additional mean credit

    c_b=max(A_b-X_b-L27_b*E27-Lge4_b*Ege4
                         -M5_b*E5d-M15_b*R5*E15d,0).

The same head must occur in C_b and c_b. Define the complete tail
numbers R_k and Zplus using125 and this same capacity vector. Then

    integral_mu f(A_test)
      <=a0*S+sum_t a_t*(R_(k_t)+Zplus)+Ma*omega
                       +max_b[C_b(theta,q)-a1*c_b].            (CC1)

Here b includes the independently chosen positive-seven root and slot.
The six old head labels, selected25/27/75/81 and all omitted labels
partition the original load exactly as in109/116. Positive hinge
coefficients allow all corresponding inequalities to be summed. The
extra mean deletion is subtracted only for the coefficient a1, using124;
all omitted integrands receive their proved full bounds from125.

The single actual omega appears in the bounded-head payment and in the
tail formulas. This pays different nonnegative integrands against the
same positive measure V-delta; it does not give each one its own rho.
Formula(CC1) is evaluated at the common actual vector throughout.

Clipping c_b at zero is legitimate for this fixed-vector maximum because
its virtual integral is nonnegative. This implementation does not infer
convexity of the clipped or nonlinear full objective. Uniform source or
shared-defect optimization remains a separate proof obligation.

The constant a0 multiplies actual S. In109's stored result the field
constant_mass_term is already a0*(53/360). Recover a0 by dividing that
stored field by53/360 before using(CC1). The original linear cost40 has
a0=1, so its constant contribution is S, including off the face. The
checker explicitly verifies this nonzero-constant case.

## 2. The complete actual398 family gives every input jointly

Use48's variant398 with all source exponents0<=a,b<=N and all positive
seven exponents1<=e<=N. The source and mixed labels are exactly its
original distinct exponent triples, not newly assigned marginals. Put

    t=sum_(a=3..N)3^-a, q=sum_(b=1..N)5^-b,
    v=7^-N, p=1-v, u=(1-v)/5,
    kappa7=(1-v)/(5+v).

The raw source parameters are

    deficit=(9t,0,0,0,0), alpha=(0,q), beta=(0,0,q,0,0),
    late=(tq,0,0,0,0), z=1-q.

Let d,n,eta,s be their actual source outputs, with D=max d=z,
h=sum eta and h1=sum_(l>=2)eta_l. The shallow carrier law is

    pi_(1,1)=p, pi_(-1,-1)=v.

Absent shallow higher depths occupy the empty carrier. The actual
source-free best-five slot has r=r1=0. Its canonical slot ordering
P,A,B,Q,H corresponds to physical residues1,2,3,0,4, and

    q_slots=(0,1/5,1/5,2/5-q,1/5),
    wrong5=wrong15=v/5.

The latter weights are precisely the absent shallow cofactor labels at
e>N. All present5 and15 old cylinders use H.

Within each of48's five mixed cofactor groups the old cylinders are
disjoint. Different group/seven-depth classes have disjoint seven
cylinders. Consequently the complete old-coordinate sum for the present
mixed labels and their actual deleted and virtual masses are

    H=4/9+t+q/9-tq,
    delta=kappa7*H, V=u*H,
    omega=(u-kappa7)*H, S=s-delta.                (CC2)

The virtual pure7-normalized cap u differs from the actual conditional
seven weight kappa7; their difference is retained rather than set to
zero. The full actual capacity is

    T=[p*(n1+n2+n3+n4)+D/18
                           +(h+h1+max eta)/4+1/72]/5,
    rho=T-delta.

Here n1 is cell1 and n2+n3+n4 is root1, so the shallow term is exactly
the stated carrier contribution. The disjoint complete defects are

    E5=h/25-u*h/5, E15=h1/25-u*h1/5,
    E3=D/90-u*D*t,
    E5d=h/100-u*h*(q-1/5),
    E15d=h1/100-u*h1*(q-1/5),
    E27=D/135-u*D/27, Ege4=E3-E27.               (CC3)

Every missing b,a or e tail stays in its displayed full capacity. The
same actual product-source weights give

    sigma=1-(18t)^2*(4q)^4*p.

At N=5 this is0.07394380607948110...<2/27 and decreases with N. Thus
N=5 and8 both satisfy the cited concentration and packing domains. Their
S values are respectively0.1496767151996587... and0.1473105298143197....
The checker verifies the common residual inequality using(CC2)--(CC3).
The source formula and disjoint original-cylinder proof are48's; this
result directly consumes them.

## 3. Exact integer compilation keeps the original LP

The reusable IntegerHead compiler evaluates precisely116's finite
operator. At fixed actual source and coefficients, take the least common
multiple of all finite head/increment denominators and a second least
common multiple for source capacities, group budgets and selected-cylinder
weights. Scaling by these two integers changes no rational value.

For each of the three original source groups, fill capacities in descending
integer objective order. If the budget is filled, the last used objective
value is a dual threshold; if it is unfilled, threshold zero suffices.
The checker verifies equality with

    gamma*budget+sum_i cap_i*(objective_i-gamma)_+

at every branch. This supplies matching feasible primal and dual values,
including zero budgets and unused capacity. The selected original-cylinder
operators keep exactly their original finite maxima. There is no floating
point arithmetic or discretization of continuous source masses.

Every head uses one load on25 cell/slot positions. Each of its10 independent
positive-seven projections changes the same local bridge before the source
and selected-cylinder maxima. The mean correction is deducted for that
same head before the global head maximum. Exact cross multiplication ranks
rational candidates, and the maximizing witness is retained.

## 4. Numerical instance and verification

The R17(0,1) coefficients are read from the pinned original109 cost record;
its all-load expansion and all affine tail coefficients are already part
of that result. The complete face upper is exactly

    18079750684152397381/11601941328182205000.

At height5 the new complete off-face upper is

    233372691189641239605463800647/148849220723720660254361250000.

At height8 it is

    147946803203080997831530511828219591054597411
        /94909427975169717001532053778975904843750000.

All three have maximizing head(0,1,2,0,2,1,2) and positive-seven root0,
slot2 within this generator. This agreement does not establish that the
maximizer stays fixed at other source data or that the true actual-family
cost attains the relaxed source maximum.

[complete_off_face_cost.py](../../frontier/comparison-bounds/complete_off_face_cost.py) and its
[certificate](../../certificates/source_norms/comparison-bounds/complete_off_face_cost.json)
retain375000 complete branch checks. At120 independently chosen branches,
the integer compiler also equals116's existing rational dual solver. The
exact face result is compared with109's already published full maximum.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/complete_off_face_cost.py --check
```

This closes the previously unspecified tail input of the common original
cost bound. A global conclusion still requires controlling the joint
nonlinear objective over every admissible actual source and shared defect
allocation, carrying all other numerator and denominator terms, and the
remaining prime continuation. The three numerical rows do not replace
any of those obligations.
