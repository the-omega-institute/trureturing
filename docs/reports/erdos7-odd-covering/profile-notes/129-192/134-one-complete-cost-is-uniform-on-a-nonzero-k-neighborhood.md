[Index](../../marked_head_profile.md) · [Whole-face source projection](../065-128/106-the-actual-denominator-shares-the-carrier-mass-residual.md) · [Finite source operator](../065-128/116-signed-face-duals-transport-one-shared-finite-source.md) · [Packing budget](../065-128/117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [Complete tails](../065-128/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md) · [Fixed affine supports](../065-128/127-complete-tail-supports-restore-one-shared-convex-budget.md) · [Corrected source modulus](133-unchanged-source-budgets-can-move-the-best-five-slot.md)

# One complete cost is uniform on a nonzero K neighborhood

The original cost1, R17(0,1) from109, has the complete bound

    Cost1 <= 21719638057873309713367061660960047
             /13922097554992082355900000000000000
           =1.560083742559701... <1.57             (UN1)

uniformly over every actual effective source satisfying

    qK>=1-sigma, 0<=sigma<=1/10000,
    0<=rho<=1/100000, 0<=r<=1/520.                 (UN2)

Here rho and r are the actual complete residual and best-five-slot
loss of117. Both K orientations, every feasible root1 beta distribution,
all original test residues, all12500 base heads, all10 positive-seven
head choices and every infinite exponent tail are included. The exact
face value is1.558338399818915..., so the uniform excess in(UN1) is
0.00174534274078570....

This is a source-uniform local consumer. It extends129's fixed-source
consumer to a nonzero continuum of actual sources. It is an ordinary
proof supplemented by exact rational arithmetic, not a Lean theorem,
a new global K, or a resolution of unrestricted Erdos #7. The enlarged
LP and residual vertices are outer relaxations; no realization of their
maximizers by actual congruence families is asserted.

## 1. Uniform geometry and the common polygon

Fix0<=delta<=2/27 and a residual radius rho0>=0. Assume the actual
source has sigma<=delta, rho<=rho0, r<=r*=1/520. Apply106's concentration
argument and choose its canonical orientation. The other orientation
exchanges cells0 and1. Put

    p=z-3/4, a=1/4-alpha1, b=1/4-sum_(l>=2)beta_l.

Then0<=p,a,b<=delta/4 and Delta=p+a+b<=3delta/4. Directly from the
single deficit budget and the concentrated carrier mass,

    eta0 in[1/18,(1+delta)/18],
    eta_l in[1/9-delta/18,1/9] for l!=0,
    h>=1/2, h1>=hmin=1/3-delta/18,
    h0<=1/6+delta/18,
    pi_(1,1)>=1-delta.                            (UN3)

117's DP13 at delta=2/27 and r*=1/520 has positive minimum
6133/568620. Thus the packing and first-label forcing guards hold
throughout this domain. In particular DP7 gives r<=5rho. It is now
legitimate to improve the radius to

    rbar=min(1/520,5rho0),
    v0=min(1/20,3delta/4+2rbar),
    v1=min(1/10,3delta/4+rbar/hmin),
    g=min(1/10-rbar,hmin/5-rbar,
          (1/9-delta/18)/5-rbar,
          hmin*(1/10-3delta/4)-2rbar)>0.             (UN4)

The lower bound hmin is written as `h1min` in the helper.
Both actual packing gaps G5,G15 are at least g. Consequently

    y=(E5-g*q5,E15-g*q15,E27,Ege4,E5d,E15d,omega)

has nonnegative coordinates, with

    sum_j y_j<=e(q)=rho0-g*(q5+q15),
    0<=q5,q15<=1/5.                               (UN5)

The first coordinate still contains r/5. No subtraction of that term
has occurred. The common polygon is the set e(q)>=0 in this square.
All seven coordinates use the same rho0 once.

The source ratios used by124 are bounded uniformly by

    t=R/(D-R)<=tbar=2(1+delta)/(1-4delta),
    C27<=Cbar=(3/4+delta/4)/(1/5-3delta/8),
    kappa=h1/(h1-h0)<=kbar=(6-delta)/(3-2delta).
                                                               (UN6)

For the first bound use R<=1/2+delta/2 and D-R>=1/4-delta. For the
second use D<=3/4+delta/4 and124's forced27 gap. For the last, writing
root1 and root0 deficits as x,y gives kappa=(3-x)/(1+y-x), where
x<=delta/2 and y>=(1-delta)/2. It increases with x and decreases with y,
so its maximum is the stated corner. Finally

    0<=z-D<=alpha0+min(beta0,beta1)<=3delta/8.      (UN7)

These bounds require no beta vertex choice.

## 2. One enlarged finite LP dominates every actual source

Relabel the first-beta cell L as2, keeping all original test labels.
Use the complete face cap table U* and its three grouped masses

    N*=(1/36,1/12,5/36)

from116. The groups are cell0, cell1 and all three root1 cells. On the
entire projected beta face these masses, the cap table, the carrier
score(0,1,1,1,1), the selected operators and the mean reference are
independent of the root1 beta distribution. In particular no numerical
scan over beta vertices is being used to infer uniformity. Some points
of the relaxed beta triangle are not realizable with a prescribed L;
this does not affect domination of every actual source.

The actual grouped masses obey N<=N*+dN with

    dN=((5delta+delta^2)/72,delta/36,delta/4).      (UN8)

For cell0, use eta0*d0-late0<=(1+delta)(3+delta)/72
-(1-delta)/72. For cell1 use eta1<=1/9 and d1<=3/4+delta/4.
For root1, d_l<=1/2+delta/2-beta_l, sum beta_l>=1/4-delta/4
and eta_l>=1/9-delta/18 give

    sum_(l>=2)n_l<=5/36+5delta/24-delta^2/72
                   <=5/36+delta/4.

The cap increases du are

| Position | du |
| --- | ---: |
| Exact excluded entry |0|
| Non-Q entry in cell0 |delta/90|
| Non-Q entry in another cell |0|
| Q in cell0 |delta/90+v0/18|
| Q in cell1 |v0/9|
| Q in root1 |v1/9|

The exclusions are P everywhere, A in root1 and B in cell L. The
ordinary bounds follow from(UN3). For Q use116's cap formulas and
r/h<=2rbar, r/h1<=rbar/hmin. The cell0 product is bounded by its face
eta increment times the full cap1/5, plus face eta times v0; this is
why no omitted delta*v0 term is needed.

For one original branch B and positive-seven labels, let Z_i*(q) be
116's face finite coefficient and

    V_i=sum_t a_t*(B_i-t)_+.

The actual carrier score is nonnegative in cell0 and at least1-delta
elsewhere. Its finite coefficient therefore obeys

    Z_i(theta,q)<=Zbar_i(q)
       =Z_i*(q)+(delta/5)*V_i*1_(cell(i)!=0).      (UN9)

Define the uniform LP with fixed caps U*+du, masses N*+dN and
coefficients Zbar(q). Every actual feasible source vector is feasible
for this enlarged LP and its coefficients dominate the actual ones.
All coefficients are nonnegative. Thus it bounds the actual head.

The four selected original-label operators are still evaluated on
exactly the face table and the same branch. With

    A_k=sum_(t:k_t>=k)a_t,

their total positive change is at most

    Esel=13delta*A1/2250
       +A2*(max(v0,v1)+delta/5)/27
       +7delta*A3/2250
       +A4*(max(v0,v1)+delta/5)/81.               (UN10)

For25, the changed cell0 descendant mass contributes at most
5delta*A1/2250 and the other four coefficient changes at most
8delta*A1/2250. For75, root0 contributes at most(5+2)delta*A3/2250;
root1 contributes at most6delta*A3/2250. For27 and81 only one Q
pre-cap grows per ternary cell, by at most max(v0,v1); the total
five-slot pre-cap is at most1 and coefficient increments grow by at
most delta*A_k/5. Division by27 or81 gives the remaining terms.

Write Cbar_B(q) for the enlarged head LP plus these exact face selected
operators, before adding Esel. Its feasible sets do not depend on q.
Its coefficients are affine in q, hence Cbar_B is convex. This proves
the needed convexity directly; no q-dependent optimized-dual
perturbation is asserted convex.

## 3. The corrected mean stays on the same head

Retain124's head features Mxi,M,N0,N1,I,J,M5,M15. Define

    Lge4=Mxi+I*(1+J)*tbar,
    L27=M+max(N0*(Cbar-1),N1*tbar).               (UN11)

Let A_B* be its face mean reference. It depends on the same head,
fixed face eta and raw slots(0,1/5,1/5,3/20,1/5), and not on beta.
133's SM13 and SM14 prove

    A_B*-(A_B-X_B)<=299delta/10800+4r/(135h),
    E5-g*q5>=r/5.

Since h>=1/2, the last term multiplied by a1 is at most

    (8a1/27)*(E5-g*q5).                           (UN12)

The price is attached to the first shifted coordinate itself. There
is no extra (8a1/27)*g*q5 payment. This corrected inequality includes
actual pure5 H/Q source migrations; no Delta-only bound on the raw
five-slot marginal is assumed.

For each branch, subtract a1*A_B* and add the source mean charge
299a1*delta/10800, while retaining the four deep defect prices

a1*L27, a1*Lge4, a1*M5 and a1*kbar*M15. No clipped mean credit is
needed for an upper bound: a negative affine lower credit is still a
valid lower bound, although weaker than zero. Maximizing only after
this subtraction retains each original head's own face slack.

## 4. Uniform complete tails and their fixed supports

In125's notation the four reference coefficients are bounded by

    cbar=(7/10+delta/4,
          2/5+13delta/90,
          4/15+delta/15,
          4/45+delta/45),

and their common raw-minus-reference envelopes by

    Hbar=(1/20+21delta/20-delta^2/5,
          1/10+(19delta+2delta^2)/90,
          1/15+delta/9,
          1/45+delta/30-delta^2/360).             (UN13)

These follow by inserting(UN3) and the carrier score bounds into125.
For completeness the needed lower reference bounds are

    c3>=7/10-4delta/5+delta^2/5,
    c5>=2/5-(7delta+delta^2)/45,
    c1>=4/15-delta/9,
    cc>=4/45-delta/30+delta^2/360.

Cell0 realizes c3: its lower advantage over cell1's upper bound is
(3delta^2-23delta+3)/20>0, and root1 has smaller availability.
For c5, couple sum eta with the distinguished score rather than
separately maximizing five independent deficits. Its lower bound
also follows from h>=1/2 and t0<=2delta, t_l<=1+delta for l!=0.
For cc, at least one of cells1--4 has deficit at most delta/8;
multiply(1-delta/8)/9 by(4-delta)/5. Subtract these lower bounds from
D<=3/4+delta/4, h<=1/2+delta/18, h1<=1/3 and max eta<=1/9 to obtain
the four Hbar entries. For the cell family, replacing its individual
references by their maximum cc and all raw coefficients by max eta
is valid before this subtraction.

The positive-seven complement satisfies

    Zplus<=779/12600+367delta/1260.                (UN14)

Indeed106 gives ||n-n*||1<=delta/2. The positive change of125's raw
C is at most delta/2+delta/2+delta/72+delta/72=37delta/36.
After division by5 this contributes37delta/180; the potentially
negative N3 movement costs at most3delta/35. The h subtraction only
helps because h>=1/2. Their sum is367delta/1260.

Choose four finite cuts N before optimizing q. For every original
prefix k_t and family p,b,O use127's exact complete support

    sum_(n>=b,n notin O) min(e,H*p^-n)<=A_N*e+B_N*H,
    L=sum_(n>=b,n notin O)p^-n.

The omitted depths are exactly the original selected labels25,27,75,81.
Let P3,P5,P1,Pc be the weighted A_N sums. The tail constant is

    T=sum_t a_t*sum_family(cbar*L+Hbar*B_N)
      +sum_t a_t*(1/72+779/12600+367delta/1260)
      +P5*delta/240.                             (UN15)

The last term uses(z-D)/90<=delta/240. No tail is discarded after
the cut; B_N is its exact infinite geometric sum.

## 5. Complete source-uniform vertex formula

Combine the previous bounds. For one branch the seven coordinate
prices are

    lambda_B=(P3+8a1/27,
              kbar*P3,
              P5+a1*L27,
              P5+a1*Lge4,
              P3+a1*M5,
              kbar*(P3+a1*M15),
              Ma+P3+P5+P1+Pc).                  (UN16)

Ma is116's bounded-head transfer price. All prices are nonnegative.
Thus the complete cost is bounded by

    max_(q in vertices(P)) max_(B,j) [
      Cbar_B(q)-a1*A_B*+Esel+299a1*delta/10800+T
      +g*P3*(q5+kbar*q15)+e(q)*lambda_(B,j)].     (UN17)

For each B,j, convexity follows from section2 and all remaining
q terms being affine. Finite maxima preserve convexity, so the
polygon vertex reduction is valid. The coordinate maximum follows
from the single simplex in(UN5). There is no independent rho budget
for each tail, head or coordinate. Different cut vectors may only be
compared after their complete maxima in(UN17).

The present original cost has a0=f(1)=0. Thus(UN17) has no surviving
mass constant. A different cost with nonzero a0 would require the
additional actual term a0*S, or the correctly oriented106 bound
S<=53/360+5delta/9+rho0 when a0>=0. The helper intentionally certifies
only the existing zero-constant cost and never silently substitutes
face mass into a nonzero constant term.

## Exact result and boundary

At delta=1/10000,rho0=1/100000 the common polygon has exactly the
vertices(0,0),(0,9/19954),(9/19954,0). The fixed cuts(8,6,6,5) give
(UN1). The maximizing branch has base layout(0,1,2,0,2,1,2), shallow
positive-seven labels(0,2), q=(0,0) and coordinate omega. Its relaxed
maximizer is not asserted realizable.

[uniform_k_neighborhood_cost.py](../../frontier/comparison-bounds/uniform_k_neighborhood_cost.py)
and its
[certificate](../../certificates/source_norms/comparison-bounds/uniform_k_neighborhood_cost.json)
evaluate375000 original branches, retain all seven residual coordinates
at each vertex and make12 independent rational/integer LP comparisons.
The genuine finite height12 family of126 satisfies
sigma=0.00003388634450980418... and rho=0.0000001883781420304623...,
so the neighborhood includes actual finite families. That example
checks the numeric inputs; the uniform quantifier is supplied by
sections1--5, not inferred from the example.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/uniform_k_neighborhood_cost.py --check
```

The local bound tends to the face value as delta,rho0 tend to zero
if the cuts tend to infinity at their geometric crossing scales.
The finite head perturbations vanish, while the complete error tails
have modulus O(delta+(delta+rho0)log(1/(delta+rho0))). A fixed finite
cut retains a positive face intercept, as127 and129 already show.
No fixed linear tail modulus or unrestricted global consequence is
claimed here. Combining this local consumer with the remaining
source regions and the original full AP comparison remains open.
