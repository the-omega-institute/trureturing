[Index](../../marked_head_profile.md) · [Complete omitted tails](../065-128/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md) · [Shared affine budget](../065-128/127-complete-tail-supports-restore-one-shared-convex-budget.md)

# One complete cost has an exhaustive shared-budget consumer

The existing original AP cost R17(0,1), cost index1 in109's complete
cost table, now has an exact consumer of127 that maximizes over every
original finite head, all seven residual coordinates and the whole
two-dimensional wrong-slot polygon. It is evaluated on126's face
reference and genuine finite398 source families of heights5 and8.

The consumer retains every infinite tail and each finite support's
positive face intercept. An independently computed complete-series
lower value matches the selected height5/height8 upper bounds. These
two supports are therefore optimal over all four-cut choices and
their convex mixtures within127's stated relaxation. At the face,
the exact infimum is approached but no finite cut attains it.

These are fixed-source upper bounds. They do not maximize over all
sources or all original AP costs, and do not give a new global K.

## 1. Actual source data and one full residual polygon

Use the actual398 source constructor of126. The selected H slot is
source-free, hence r=r1=0. Let U_(l,j) be116's actual source cap table,
with H=4 and the other first-five slots0,1,2,3. The following prices
are justified directly by that table:

    g5=h/5-max_(j!=4)sum_l U_(l,j),
    g15=h1/5-max(max_(j!=4)sum_(l>=2)U_(l,j),
                                 max_j sum_(l<2)U_(l,j)).

The first expression bounds every wrong pure5 slot. The second also
includes a15 carrier in root0, even if it uses the same first-five
slot as H. Absent labels have zero mass and obey these prices as well.
For all three specified source cases the exact values are

    g5=g15=1/45.                                  (EC1)

The constructor supplies the actual survivor mass S and the single
residual rho. In these cases45*rho<=1/5, so the complete polygon
vertices are

    (0,0), (45*rho,0), (0,45*rho).                 (EC2)

At the face rho=0 these collapse to one vertex. The positive-height
cases each have three vertices. The residual at a vertex q is
e(q)=rho-(q5+q15)/45. The computation allows the entire shared residual
simplex of127, not just the actual defect allocation of126.

## 2. Five exhaustive head maxima serve every support choice

The original six-label head has12500 layouts. Its independent
shallow positive-seven root/slot pair has10 choices, giving125000
original branches per polygon vertex. The selected25,27,75,81
operators remain the complete independently labelled operators of116;
no equality with forbidden-family residues is imposed.

For one fixed source, polygon vertex and the nonnegative coefficient
a1 of the mean term, define

    H0=max_b[C_b(theta,q)-a1*(A_b-X_b)],
    Hj=max_b[C_b(theta,q)-a1*(A_b-X_b)
                                        +e(q)*a1*L_(b,j)],  (EC3)

where j ranges over27,ge4,deep5,deep15. The four L values are exactly
124's prices L27,Lge4,M5,kappa*M15. Thus the seven-coordinate head
vector is

    (H0,H0,H27,Hge4,Hdeep5,Hdeep15,H0).            (EC4)

The finite C_b depends on the independent positive-seven pair,
while A_b-X_b and the four prices depend only on the six-label layout.
For each layout, maximizing C_b over all10 pairs therefore preserves
the same-head credit in(EC3). No mean credit from a different layout
is substituted.

Crucially, none of(EC3) depends on the four tail cuts. It can be
computed once for each source and vertex. The integer version of126's
head operator gives exact C_b values. A common integer denominator
then makes all five maxima exact integer comparisons, including the
source-error term X_b and the common residual e(q).

For a fixed support, let B and P3,P5,P1,Pc be127's complete-tail
constant and slopes. Its tail-only prices in the seven coordinates are

    p=(P3,kappa*P3,P5,P5,P3,kappa*P3,
                                      Ma+P3+P5+P1+Pc).

The complete support upper at q is therefore

    U_N(q)=a0*S+B+P3*g5*q5+kappa*P3*g15*q15
                                   +max_j[Hj+e(q)*p_j].     (EC5)

Here Hj means the seven-entry vector(EC4), and Ma is116's bounded
transfer price. Equation(EC5) is127's full same-head formula, with
r=r1=0, rearranged without weakening its maximum. In particular B
still includes P5*(z-D)/90; it is distinct from the source correction
already included in X_b.

## 3. A finite choice of complete supports

Each tested support is globally valid on the entire defect polygon
for its fixed source. Candidate cuts include the complete-family
crossings from125, the uniform cut vectors(10,10,10,10),
(12,12,12,12),(16,16,16,16), and a local integer stencil around
crossings computed from the full residual budget.

For that stencil, the family error upper bounds are

    (kappa*rho, rho+(z-D)/90, rho, rho).

They follow from one common budget and kappa>=1. These values only
select useful cuts; the evaluated objective still uses the seven
shared residual coordinates in(EC5). For each family, the stencil
uses the crossing and its immediate neighboring integer cuts, subject
to the family's minimum depth. Zero error uses finite center10.

After removing duplicate cut vectors, the face has84 candidates and
each positive-height source has85. For each candidate the program
first computes

    M_N=max_(q in Vertices(P))U_N(q),

then takes min_N M_N. It does not take a pointwise minimum of supports
before the polygon maximum. The finite candidate search alone does
not establish optimality over all cuts; section5 supplies a separate
complete-series lower value that proves it for the two positive-height
cases.

## 4. Exact complete-cost results

All values are exact rationals in the certificate. The following
decimal displays are rounded for readability.

| Source | Selected cuts(pure3,pure5,root5,cell5) | Complete shared-budget upper |126 actual-defect upper |
| --- | --- | ---: | ---: |
| Face reference |(16,16,16,16)|1.558338411403|1.558338399819|
| Height5 |(5,4,4,3)|1.596097991426|1.567846241015|
| Height8 |(8,6,6,5)|1.560624589028|1.558820934436|

For example, the exact height5 and height8 upper bounds are

    50040424450190247635241689153
      /31351724467416195405688125000,

    2878146993338780050263351316666125503
      /1844227633969899023981742012656250000.      (EC6)

Both positive-height maxima occur at q=(0,0), with the residual
assigned to the omega coordinate in the relaxed simplex. Their
same original maximizing layout is

    (r3,c9,s5,r15,s15,c45,s45)=(0,1,2,0,2,1,2),
    (positive7 root,positive7 slot)=(0,2).

The final witness is checked against127's direct `branch_affine`
and `evaluate_branch` result, so its finite head, mean credit, tail
support and residual payment belong to one original branch.

At the face the excess over126 is exactly the retained infinite
geometric intercept of the finite cuts, approximately1.15840824e-8.
It is not rounded away or reported as exact face recovery. The
height5 and height8 excesses over126 are approximately0.0282517504
and0.00180365459 respectively. Their chosen supports' excess on the
actual tail allocations is approximately0.00380516358 and0.000164874358.
The total comparison also enlarges the actual allocation to the whole
simplex and uses the affine mean credit; it is not attributed solely
to the tail support or to omega.

Thus this consumer quantifies the price of discarding the known
actual defect allocation while retaining a sound full-budget upper.
It does not improve126's more specialized actual-allocation numbers.
The off-face maximizing omega coordinate is an outcome of the
relaxation. No actual-family realization of that extreme allocation
is asserted.

## 5. A matching lower value proves optimality over every cut vector

Fix q=(0,0) and assign all residual to omega:

    y=(0,0,0,0,0,0,rho).

This point is feasible in127's shared simplex. All four extra mean
defects vanish, so its exhaustive finite-head value is H0 from(EC3).
The four complete nonlinear family errors at this point are

    (rho,rho+(z-D)/90,rho,rho).                    (EC7)

In particular the first is rho, rather than the larger kappa*rho
used to choose the initial search stencil. Evaluate each punctured
series directly using125's exact complete geometric summation,
with127's collapsed cell reference. Include the complete mixed and
positive-seven terms; call the resulting weighted tail Tomega.
Define

    Lomega=a0*S+H0(q=0)+Ma*rho+Tomega.             (EC8)

Every affine support majorizes its complete family at this same
point. Consequently, for every cut vector N, including those never
enumerated by the program,

    max_q U_N(q)>=U_N(0)>=Lomega.                 (EC9)

An independent crossing calculation for(EC7) gives precisely
(5,4,4,3) at height5 and(8,6,6,5) at height8. In each case the
exact rational Lomega equals the selected whole-polygon upper in
(EC6). The lower value and the exhaustive upper therefore match:

    inf_(all cut vectors N) max_q U_N(q)=Lomega,   (EC10)

and these finite cut vectors attain the infimum. Every convex
mixture of supports also has value at least Lomega at the same
q=0, omega=rho point, so mixing cannot improve this number.

There is a further scoped interpretation. Define the nonlinear
relaxed objective by retaining the exact four complete family
errors, the collapsed cell cap, the finite-head C_b upper, the affine
mean credit and127's entire shared simplex. The point used in(EC8)
attains Lomega in that relaxation, while the selected supports bound
every relaxed point by Lomega. Thus its nonlinear relaxed maximum
also equals Lomega at these two sources. This lower value concerns
the algebraic comparison scheme; it is not an actual-cost lower
bound or a construction of an original covering.

At the face rho=0 and z-D=0, the same computation gives

    Lomega=18079750684152397381/11601941328182205000,

exactly126's face value. Uniform cuts tending to infinity approach
it, but every finite cut leaves a positive complete-tail intercept.
The selected cut16 excess is exactly

    59180320631/5108762054443359375.

The remaining height5/height8 gap to126's actual-allocation upper
cannot be removed by searching more cuts or mixing them within
this fixed relaxation. An improved bound must retain an additional
valid restriction or strengthen one of its input estimates.

## 6. Verification and remaining scope

[exhaustive_shared_tail_cost.py](../../frontier/source-budgets/exhaustive_shared_tail_cost.py)
pins126's actual source/cost implementation,127's support interface
and the exact126 comparison certificate. It enumerates875000 original
branches across the seven polygon vertices, with140 independent
rational/integer coordinate comparisons. The complete finite-objective
digests, all support values, polygon vertices, exact maximizing
witnesses and independent complete-series optimality lower values are in the
[certificate](../../certificates/source_norms/source-budgets/exhaustive_shared_tail_cost.json).

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/exhaustive_shared_tail_cost.py --check
```

No original head is omitted from these specified cost/source maxima.
The three source data, however, are not the full source domain.
Extending this calculation to source neighborhoods and the complete
cost vector remains necessary before a new global comparison can be
claimed. No Lean verification or unrestricted Erdős #7 resolution
is asserted.
