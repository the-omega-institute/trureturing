[Index](../../marked_head_profile.md) · [Whole face consumer](../065-128/113-quadratic-hinges-and-the-factorial-tail-share-one-head.md) · [Independent indicators](152-independent-shallow-indicators-sharpen-the-complete-mean-and-square.md) · [Complete neighborhood](160-one-actual-residual-closes-a-hundredfold-wider-neighborhood.md) · [Stronger inner heavy bounds](162-fixed-supports-preserve-both-heavy-margins-on-the-source-slab.md) · [Sharp joint moments](164-the-pure-five-first-and-second-moments-have-a-sharp-joint-envelope.md)

# The pure-five joint envelope enters both complete comparisons

The joint pure-five moment theorem164 improves the full52-cost
comparison on the whole saturated faces. A separate transport
argument also improves both complete residual shells of160,
retaining162's stronger inner heavy bounds:

| Actual source domain | Previous complete comparison | New complete comparison |
| --- | ---: | ---: |
| Both whole saturated faces |459.13982857475637|459.0991409076946|
| sigma<=1/27, rho<=1/20000, r<=1/4000 |473.11203393433925|473.09280433220545|
| sigma<=1/27, 1/20000<=rho<=1/1000, r<=1/520 |508.9706821709662|508.9604579570802|

The last two closed shells therefore give the complete neighborhood
bound508.9604579570802. Each comparison retains all52 independent
original costs, the actual mass coefficient, all complete square
categories, the entire denominator and every infinite tail.

These ordinary proofs and exact rational computations do not
resolve unrestricted Erdos7 or supply a new global K. In particular,
163's controlling outer source strip is unchanged. The three
comparisons remain above the sufficient threshold403. No Lean or
frozen-state claim is made.

## 1. Replace exactly one complete LCM category on the face

Let Y=sum_(b>=1)1_(F_b) be the independently labelled pure-five
test from164. Write the whole original load as A=1+Y+Z, where Z
contains every test having a positive ternary or seven exponent.
Then Y^2+2Y is exactly the nonunit part whose two test labels both
have ternary and seven exponents zero. The unit square S and all
terms involving Z are retained.

For one prime coordinate, the number of ordered exponent pairs
with maximum b is(b+1)^2-b^2=2b+1. Therefore the old bound for
this category in143 was

    Uold=3*(14/225)+(2/5)*sum_(b>=2)(2b+1)*5^-b
        =89/300.

164 at lambda=2 replaces this whole category by49/180. Thus

    Uold-Unew=11/450,
    Qold=374/75,
    Qnew=2233/450.                              (JC1)

The zero-seven subtotal becomes4607/1800; the complete positive-seven
subtotal stays(2/3)*(173/48)=173/72. Their sum is Qnew. Pairs
between pure-five and ternary tests belong to positive-ternary LCM
categories and are not subtracted again. The checker independently
enumerates the ordered exponent partition through coordinate4;
the product formula above proves the same partition at every depth.

## 2. Consume the new square in the strongest complete face vector

Use113's52 already accepted cost bounds and original positive
weights, mass D=53/360, linear bound L=1151/1800, negative mass
coefficient r_mass, and positive square coefficient

    cQ=2061512697931813067/15514910048663625600.

Substitute Qnew in every existing all-load majorant. All52 are
verified, including their eventual polynomial tails. None lowers
an already accepted cost bound. Consequently the only gain here is
the direct square gain; no unachieved propagation gain is counted:

    Nnew=r_mass*D+sum_(i=0..51)weight_i*cost_i+cQ*Qnew,
    Nold-Nnew=cQ*(11/450)
      =2061512697931813067/634700865627148320000.

The complete denominator is reconstructed from the same four
AP11 blocks, full count remainder and independent AP13 penalty:

    d=50511415637/632754738000>0.

The unchanged offset C0 gives

    C0+Nnew/d
      =13014078781047502133272038080082266672657503
        /28346990053863075922188555569458332750000
      =459.0991409076946... .                   (JC2)

The improvement is0.04068766706174943..., measured against113,
with all its stronger quadratic bounds retained. No finite head
scan is repeated; these are new exact substitutions into accepted
complete inequalities.

## 3. Transport the slot densities on the actual source

The fixed face saving11/450 is not assumed to persist. Use160's
actual source neighborhood, writing its source radius as delta,
its residual radius as R, and retaining actual rho<=R. Let eta,
q, Lambda, mu, a_l and the nonnegative projection defect Xi be
exactly125's objects. Its pure-five projection argument gives

    mu^5 <= (a Lambda)^5-q/90+Xi+W^5,
    (Xi+W^5)(1)=E3+(z-D)/90+omega.              (JC3)

Here a_l=1-t_l/5, and the same positive shallow3/9 weighting a is
used throughout. Source exclusion is exact: inside slot A, Lambda
has no root1 points; inside slot B, it has no points in the actual
first-beta cell L. Therefore bounding(a Lambda)^5 by the product
source eta tensor q in(JC3) yields the respective coefficients

    c5-sum_(l>=2)eta_l*a_l,
    c5-eta_L*a_L,
    c5=sum_l eta_l*a_l-1/90.                    (JC4)

This repeats the same measure inequality with fewer source cells;
it does not subtract a second copy of the forbidden family.
On Q and H retain the original c5 coefficient. P is exactly empty.

134's common-carrier and concentration bounds give, for l>=2,

    a_l>=(4-delta)/5,
    h1>=1/3-delta/18,
    eta_L>=1/9-delta/18,
    c5<=cbar=2/5+13delta/90,
    h<=hbar=1/2+delta/18,
    (z-D)/90<=delta/240.

Thus a valid positive reference density on slots(P,A,B,Q,H) is

    c_P=0,
    c_A=cbar-((4-delta)/5)*(1/3-delta/18),
    c_B=cbar-((4-delta)/5)*(1/9-delta/18),
    c_Q=c_H=cbar.                               (JC5)

All four nonzero coefficients lie between0 and hbar on the stated
domain. The H reference is weaker than164's face bound, but avoids
requiring a face-only product identity away from saturation.

Let nu be the positive part of the difference between mu^5 and
the piecewise Haar reference(JC5). Equation(JC3) on each disjoint
slot proves nu<=Xi+W^5. The raw bound mu^5<=h q<=hbar Haar also
gives

    nu(1)<=E3+omega+delta/240,
    nu<=H Haar,
    H=hbar-min(c_A,c_B,c_Q,c_H).                 (JC6)

The same positive nu works for every independently chosen deep
test. No independent defect measure is selected at different depths.

## 4. Couple the first indicator and all deep errors to one residual

For a first test in slot j,164's discounted allocation proof with
lambda=2 applies to the reference densities(JC5). Its complete deep
contribution is at most

    V_j=max_k[(11 if k=j else7)*c_k/40].         (JC7)

The coefficient multiplying nu(F_b) is at most2b+1. Hence its
remaining complete contribution is bounded by

    G(e,H)=sum_(b>=2)(2b+1)*min(e,H*5^-b),
    e=E3+omega+delta/240.                       (JC8)

For e>0, let N be the first n>=2 with H*5^-n<=e. Exactly,

    G(e,H)=(N^2-4)e+H*sum_(b>=N)(2b+1)*5^-b.   (JC9)

The last sum is the full geometric tail. At e=0, G=0.

Use152's independent first-indicator bound before its residual
maximum. For each actual first-beta cell and test slot j it has
the form

    mu(F_1)<=A_j+sum_i p_(j,i)y_i+qprice_j*(q5+q15),

with the actual seven coordinates

    y=(E5-gq5,E15-gq15,E27,Ege4,E5deep,E15deep,omega),
    sum_i y_i+g*(q5+q15)<=R.

160 checks the guards and transports these indicator bounds over
its larger residual domain. Put x=y_2+y_3+y_6=E3+omega. Define

    pin_j=max(p_(j,2),p_(j,3),p_(j,6)),
    pout_j=max(p_(j,0),p_(j,1),p_(j,4),p_(j,5),qprice_j/g).

Since the first test has coefficient3 in Y^2+2Y, one common
simplex gives the complete bound

    integral(Y^2+2Y)
      <=max_j {3A_j+V_j+
          max_(0<=x<=R)[3pin_j*x+3pout_j*(R-x)
                                      +G(delta/240+x,H)]}.    (JC10)

Take the maximum over the three possible first-beta cells as well.
For first slot P, use its exact zero first mass and zero first
prices. The deep bound and error remain valid.

The inner maximum is a continuous concave piecewise affine
function. Its endpoints and every breakpoint H*5^-n-delta/240
inside[0,R] suffice. At delta>0 only finitely many exist. At
delta=0, sufficiently small x have nonnegative slope because the
G slope is N^2-4, so the infinitely many remaining near-zero knots
cannot exceed their retained upper endpoint. The program checks
that slope before omitting them. At delta=R=0,(JC10) recovers49/180.

This allocation uses the same E3+omega in the first indicator and
all tail terms. Taking a separate full residual budget for each
part is not needed.

## 5. Both existing complete shells improve on their own source

At delta=1/27,(JC10) yields:

| R | Old pure-five block | New pure-five block | Complete square saving |
| --- | ---: | ---: | ---: |
|1/20000|40189603/131220000|96744191/328050000|7459633/656100000|
|1/1000|44959573/140842800|1915283629/6111571500|997939583/171124002000|

In both rows the largest bound uses first slot Q, uniformly over
the three first-beta cells. For the outer row the maximizing
allocation is the interior breakpoint

    x=137951/328050000,

so merely inspecting the two residual endpoints would miss the
correct maximum. The first-row maximizer is x=R.

For each shell separately, replace only its old pure-five square
block by the new one. Its complete square decreases respectively
from5.194022675170192 to5.182653016581563, and from
5.379777606099303 to5.373945930990396. All other square categories
and the actual unit-mass term S remain as before.

Write the original complete signed endpoint, denominator at the
mass floor and actual-S coefficient as N,d,M, and let ell be the
shell's actual residual lower bound. The new comparison is exactly

    T=C0+[N-cQ*saving+M*ell]/[d+cE*ell],
    cE=1-1/614922.                              (JC11)

The inner row reconstructs162's whole consumer and takes ell=0.
The outer row retains160's consumer and takes ell=1/20000. The
new remaining actual-S coefficients are respectively
382.65007282459686... and418.51766812068587..., both positive.
Thus the original signed comparison and its residual-floor step
remain valid. The exact identity

    (T-C0)*d-(N-cQ*saving)+[(T-C0)cE-M]*ell=0

is checked in both rows. Every original cost index0,...,51 appears
once; the denominator and complete heads are unchanged.

The [helper](../../frontier/comparison-bounds/pure_five_complete_face_comparison.py) and
[certificate](../../certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json)
bind the original complete inputs, verify the52 all-load face
majorants, reconstruct162's inner consumer, and evaluate every
residual breakpoint of(JC10). The retained tails are exact infinite
sums. No new original-head enumeration is used.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/comparison-bounds/pure_five_complete_face_comparison.py --check
```
