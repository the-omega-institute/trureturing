[Index](../../marked_head_profile.md) · [Original heavy tests](225-two-original-tests-share-the-complete-retained-bridge.md) · [Original survival tests](226-the-joint135125-records-strengthen-two-complete-survival-bounds.md) · [Complete row transport](230-the-complete-retained-duals-share-one-raw-source-support.md)

# Fixed supports transport the complete punctured tails

A finite affine support transports the complete infinite tails of225/226
using the same seven residual coordinates as230. Its prices are added to
the fixed dual's prices before taking the shared residual maximum. Each
cut vector is fixed on the whole source domain; only then may a finite
library of such bounds be minimized.

The reusable evaluator is consumed by the four original objectives in225/226,
their eight maximizing-controller duals, and both source domains of208.
It computes16 complete fixed-row-plus-tail bounds from81 supports each.
This does not transport every other controller or the pruned two/four/six
alternatives. It is not a complete off-face head,52-cost K comparison,
actual-family attainment result, Lean result or unrestricted Erdos7 result.

## 1. One common residual and four complete exponent families

Use208's proved domains

    (d,R,G)=(1/20,1/1000,1/60),
    (d,R,G)=(1/12,1/3000,53/2700),
    kappa=(6-d)/(3-2d).

The actual residual rho ranges over[0,R]. In the order used below,

    Y=(E5-Gq5,E15-Gq15,E27,Ege4,E5d,E15d,omega),
    Y>=0, sum Y<=rho-G(q5+q15).                    (PT1)

The four zero-seven families, ordered(pure3,pure5,root5,cell5), have
bases(3,5,5,5) and original starting depths(3,2,2,2). The complete
min-geometric bounds in125,134,157 and195 admit the uniform coefficients

    cbar=(7/10+d/4,2/5+13d/90,4/15+d/15,4/45+d/45),
    rawbar=(3/4+d/4,1/2+d/18,1/3,1/9),
    Hbar=rawbar-cbar
        =(1/20,1/10-4d/45,(1-d)/15,(1-d)/45).      (PT2)

For example, availability and the shallow carrier give
c3<=7/10+d/4. The nonzero-cell coefficient obeys
a_c<=(4+d)/5, while eta0<=(1+d)/18 and eta_c<=1/9
elsewhere. These imply the other three reference bounds in(PT2).
The cell0 alternative is smaller by(1-d)/30. The root0 branch is
dominated before replacement, because

    c1-h0>=1/30-4d/45>=7/270>0.

The safe replacement is justified by the monotonicity of

    min(c*x+e,raw*x)

in c,e,raw separately. It does not require the generally invalid
inference raw-c<=rawbar-cbar from the separate upper bounds.
The resulting family errors use precisely(PT1):

    e3=Gq5+kappa*Gq15+Y1+kappa*Y2+Y5+kappa*Y6+Y7,
    e5=d/240+Y3+Y4+Y7,
    e15=e45=Y7.                                   (PT3)

The term d/240 comes from(z-D)/90<=3d/(8*90). The full shallow
E5,E15 and their disjoint deep families remain in e3. No eighth
defect and no additional copy of rho are introduced.

## 2. Puncture the original exponent series

For the first hinge t=1 there are no selected-label omissions.
For t>=2 the retained labels are25,27,75,81,135,125.

|Family|Original depth|Omitted depths at t>=2|Remaining first depth|Unpunctured mass|Punctured mass|
|---|---:|---|---:|---:|---:|
|pure3|3|3,4|5|1/18|1/162|
|pure5|2|2,3|4|1/20|1/500|
|root5|2|2|3|1/20|1/100|
|cell5|2|none|2|1/20|1/20|

In particular125 is removed at depth3 of the actual pure-five
series. Subtracting its face value2/625 from an off-face bound
would not be the same operation. The retained135 removes the
assigned raw cap1/135 from the mixed series1/72, leaving7/1080.
All other mixed labels remain in that sum.

The full positive-seven complement after retaining the six
projections21,35,63,105,147,245 is

    Z6=N3/245+N9/35+D/90+53h/4900
                         +11h1/700+em/20+1/360.  (PT4)

The new147,245 assignments remove6N3/245 and6h/1225 from208's
four-projection series. Unit7^e terms remain in the complete head;
the other unretained positive-seven labels remain in(PT4).
At the face Z6*=2669/88200. Substituting158's scalar source bounds
into(PT4) gives, in loss order(u_a,u_z,u_b,u_d,u_l,u_p),

    p6=(1/2940,23/5880,1/8820,29/44100,0,0).

The exposed-coordinate price gap is

    (11/12)*(23/5880)-29/44100=1033/352800>0.

Thus156's common source-loss bound gives

    Z6<=2669/88200+23d/5880,                     (PT5)

equal to307/10080 and1199/39200 on the respective domains.
This is one source-loss support, not separate uses of d for each term.

## 3. Fixed cuts include the entire geometric continuation

For base p, original depth b, finite omitted set O and integer N>=b,
write

    L=p^(1-b)/(p-1)-sum_(o in O)p^(-o),
    A(N)=#{n:b<=n<N,n notin O},
    B(N)=p^(1-N)/(p-1)-sum_(o in O,o>=N)p^(-o).

For e,H>=0,

    sum_(n>=b,n notin O)min(e,H*p^(-n))
                      <=A(N)*e+B(N)*H.           (PT6)

Use the e branch before N and the geometric branch from N onward.
The latter is the exact infinite continuation. There is no finite
exponent truncation. When e>0, the first N with e*p^N>=H attains
equality, including when the crossing depth itself is omitted.

All current omissions are initial prefixes. If b' is the first
remaining depth, the executable formula is

    L=p^(1-b')/(p-1),
    A(N)=max(N-b',0),
    B(N)=p^(1-max(N,b'))/(p-1).                  (PT7)

For e=0,H>0 the infimum over finite cuts is zero, but no finite
cut attains it. Consequently a finite support has a positive face
intercept above the exact face tail for a nonzero hinge objective.
It is not a zero-intercept continuity estimate.

## 4. Compile the tail into the seven existing prices

For original nonnegative hinge coefficients a_t, let

    w0=a1, w6=sum_(t>=2)a_t, w=w0+w6.

Choose four cuts in each occurrence class, unpunctured and punctured.
For family j put

    ell_j=w0*L_j0+w6*L_j6,
    m_j=w0*A_j0+w6*A_j6,
    b_j=w0*B_j0+w6*B_j6.

The complete tail support is

    Tail<=Ctail+G*m3*q5+kappa*G*m3*q15+tau.Y,     (PT8)

where

    Ctail=sum_j(cbar_j*ell_j+Hbar_j*b_j)
          +(d/240)*m5+w0/72+7*w6/1080
          +w*(2669/88200+23d/5880),
    tau=(m3,kappa*m3,m5,m5,m3,kappa*m3,
                                      m3+m5+m15+m45).

This follows by substituting(PT3) into(PT6), adding the specified
mixed series and(PT5). The original exact face tail is

    Tface=w0*(163/1800+2669/88200)
              +w6*(7579/405000+2669/88200).      (PT9)

The executable compares(PT9) with each original225/226 controller's
stored complete tail. Starting with its raw dual objective, it adds
(PT8) exactly once. Equivalently, starting with its complete face
branch, it replaces Tface by(PT8).

## 5. Join rows and tails before using the residual budget

Let230's fixed row record supply source Cfixed, signed raw-polytope
support J(q), and seven prices lambda. Its proved specialization has
zero survivor-mass price. For a fixed cut vector put

    Lambda=max_i(lambda_i+tau_i).

The combined row-error-plus-tail bound is

    Cfixed+Ctail+J(q)+G*m3*q5+kappa*G*m3*q15
                    +(R-G(q5+q15))*Lambda.       (PT10)

The single maximum is taken after addition. Taking separate maxima
for lambda and tau loses their shared-budget relation.
The raw support J is convex in q because its25-node feasible
polytope is fixed. The remaining terms are affine. The maximum
of(PT10) on the whole triangle is therefore attained among

    (q5,q15)=(0,0),(R/G,0),(0,R/G).              (PT11)

Replacing actual rho by R is legitimate because Lambda>=0 and
the survivor-mass price is zero. A future signed survivor-mass
extension requires its own term and the fourth vertex(0,0,0) in
(q5,q15,rho); the present API does not claim that extension.

Only after evaluating all three vertices for one fixed support
does the program minimize over the candidate library. The order
cannot be interchanged. For example the two complete p=2 geometric
tails with errors e,1/2-e have value3/2 at e=1/4. Their valid fixed
supports2e+5/4 and9/4-2e have endpoint maximum after pointwise
minimization5/4, which would be false on the interior. Minimizing
their individual endpoint maxima instead gives the valid9/4.

## 6. Actual consumer and exact results

The program reads the two original heavy objective vectors at
indices0,16 directly from225, and the AP13 and AP11 block0 vectors
from226. Their weights are not rounded or substituted. AP13 uses
only a4=1; AP11 block0 uses

    a1=1355/263538, a2=20425/263538,
    a3=25/363, a5=28/33.

For each original maximizing layout and projection tuple, both
nested/disjoint controller duals are read by their original keys.
The current complete row prices are rebuilt for only those eight
duals. Their exact dual RHS values and the full7163-row/56-equality
inventory are checked against the original branch matrices. Original
dual-column feasibility is inherited from the pinned225/226
certificates; no new head/projection scan is run.

Candidate generation starts at the first cuts not uniformly
dominated by advancing one retained depth. The comparison uses
error maxima(kappa*R,R+d/240,R,R). The initial vectors are

|Domain|Unpunctured|Punctured|
|---|---|---|
|d=1/20|3,3,3,2|5,4,3,2|
|d=1/12|4,4,4,3|5,4,4,3|

For each family independently add0,1 or2 to both of its occurrence
cuts. This defines the actual81-element library. It is not a claim
of global cut optimality or of independence between the two
occurrence classes. The selected offsets are(0,0,1,1) for the two
heavy objectives on d=1/20, all zero for them on d=1/12, and
(0,0,2,2) for both survival objectives on both domains.

The following are decimal readings of exact certificate values,
after adding the original raw dual objective and taking the maximum
of the two separately bounded geometric alternatives:

|Original controller objective|d=1/20,R=1/1000|d=1/12,R=1/3000|
|---|---:|---:|
|heavy0|6.119973059859|6.023944548395|
|heavy16|4.877010002917|4.794068033015|
|AP13|0.219643559679|0.210459887754|
|AP11 block0|0.197769973144|0.190669204579|

These are fixed-controller row-plus-tail bounds, not uniform bounds
over all original heads. The certificate separately stores each
branch's exact increment over its original complete face value,
so a later complete comparison can replace the tail without
double counting it.

The selected supports improve the initial library candidate in12
of the16 controller-domain cases. This is an actual support choice
in the calculation. All1296 candidate-domain bounds and the selected
raw primal/dual witnesses are retained as exact rationals.

## 7. Reusable program and boundary

`frontier/retained-transport/retained_punctured_tail_support.py` exposes:

- `compile_tail_support(d, hinge_coefficients, cuts)`: the complete
  tail intercept, wrong-slot coefficients and seven primitive prices;
- `evaluate_row_support(row, parameters, caps, budgets, bridge, support)`:
  a current230 row and one fixed support on the complete domain;
- `choose_support(..., hinge_coefficients, candidates)`: the finite
  minimum of complete-domain bounds, with the selected cuts and witnesses.

`parameters` supplies delta=d,rho=R,gap=G. The raw caps and three
budgets must describe the same proved containing polytope as the
row record. Source guards are checked for the two actual consumers;
an arbitrary new domain still needs its own source proof.

The standalone certificate is
`certificates/source_norms/retained-transport/retained_punctured_tail_support.json`.
It depends on source programs and pinned original certificates,
without depending on230's output certificate. Canonical split
certificate reads and writes use `certificate_io`.

Validation checks the exact certificate regeneration, independently
recomputes all1296 bounds, solves112 raw LPs by dual-breakpoint
minimization, and compares576 direct complete-tail evaluations
with the compiled shared-budget support, including joint interior
points. Those finite checks complement the full-series proof(PT6);
they do not replace it. Other duals, old pruning branches and the
complete off-face consumer remain separate obligations.
