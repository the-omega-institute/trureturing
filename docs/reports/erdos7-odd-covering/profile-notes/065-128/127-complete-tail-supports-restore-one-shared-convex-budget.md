[Index](../../marked_head_profile.md) · [Finite convex source](116-signed-face-duals-transport-one-shared-finite-source.md) · [Packing prices](117-the-actual-slot-defects-share-a-stronger-packing-polytope.md) · [One-head mean correction](124-one-original-head-transports-the-whole-deep-mean-credit.md) · [Complete omitted tails](125-the-complete-off-face-omitted-tails-recover-every-face-constant.md)

# Complete-tail supports restore one shared convex budget

Every complete geometric error in125 has explicit affine upper
supports after removal of its selected original labels. Fixing four
integer cuts replaces the nonlinear tail errors by linear prices on
the existing common defect vector. Adding124's same-head mean credit
then restores a valid convex optimization in116's two wrong-slot
weights. The cuts do not truncate the tails: their intercepts retain
the exact infinite geometric remainders.

For several nonnegative weighted costs, the common residual can be
eliminated using only seven choices of a shared defect coordinate.
After that choice, the independent original-head maximum separates
by cost. This avoids both independent copies of the residual budget
and an exponential Cartesian inventory of cost-head tuples.

The theorem is conditional on the actual source, packing prices and
concentrated domain of116/117/124. It supplies an optimization bridge,
not the maximum over all sources, a new global K, or a Lean result.

## 1. Affine supports of complete punctured geometric series

For p>1, integer b>=0 and a finite set O of removed depths n>=b,
define, for e,H>=0,

    G_p^O(e,H;b)=sum_(n>=b,n notin O)min(e,H*p^-n).

Choose an integer N>=b, and put

    A_N=N-b-|O intersect[b,N)|,
    B_N=p^-N/(1-p^-1)-sum_(n in O,n>=N)p^-n,
    L=p^-b/(1-p^-1)-sum_(n in O)p^-n.

The exact complete-tail support is

    G_p^O(e,H;b)<=A_N*e+B_N*H.                   (AS1)

For every retained n<N, use min(e,H*p^-n)<=e; for n>=N use the
other bound. Summing the latter indices gives precisely B_N, with
no omitted infinite remainder. The selected original depths are
removed before either summation. All three coefficients are
nonnegative. The reference-plus-error family consequently obeys

    sum_(n>=b,n notin O)[c*p^-n+min(e,H*p^-n)]
                      <=c*L+A_N*e+B_N*H.         (AS2)

For e>0, taking N at the first crossing H*p^-N<=e gives equality
in(AS1), even when some crossing indices belong to O. For e=0,
letting N tend to infinity makes B_N*H tend to zero. Thus

    G_p^O(e,H;b)=inf_(N>=b)(A_N*e+B_N*H).         (AS3)

For a given family one common crossing works for all prefix
omissions. Four cuts, one per family, therefore suffice; different
cuts for different hinge thresholds are not required for exact
attainment of the collapsed family's infimum.

## 2. The four positive reference families

Use125's c3,c5,c1, D,h,h1,kappa and its actual defect vector. In
the concentrated domain h0<c1, so the raw root0 branch is dominated.
For the cell family define

    cc=max_l(eta_l*a_l), hm=max_l eta_l.

Its individual cell caps satisfy

    max_l min(eta_l*5^-n,eta_l*a_l*5^-n+omega)
                 <=min(hm*5^-n,cc*5^-n+omega).

The resulting single cell envelope retains the entire family and
agrees with125 on the saturated face. The complete four-family data
to use in(AS2) are

| Family | p | b | c | H | e |
| --- | ---: | ---: | --- | --- | --- |
| pure3 | 3 | 3 | c3 | D-c3 | E5+E5d+kappa*(E15+E15d)+omega |
| pure5 | 5 | 2 | c5 | h-c5 | E3+(z-D)/90+omega |
| root-five | 5 | 2 | c1 | h1-c1 | omega |
| cell-five | 5 | 2 | cc | hm-cc | omega |

The cell collapse may weaken125 away from the face. The other
three families retain its exact single-branch caps. Source data
are fixed in this table; affineness here is in the defect vector,
not in all source parameters.

For a nonnegative hinge combination a_t,1<=t<=8, let
k_t=min(t-1,4). Keep125's omissions: pure3 omits3 if k>=2 and4
if k>=4; pure5 omits2 if k>=1; root-five omits2 if k>=3; cell-five
omits nothing. Choose cuts N3,N5,N1,Nc. For each family j put

    P_j=sum_t a_t*A_(j,N_j,O_(j,k_t)).

Let B be the sum of all c*L+B_N*H terms in(AS2), with the same
a_t weights, plus

    sum_t a_t*(1/72+Zplus)+P5*(z-D)/90.           (AS4)

The1/72 is the entire deep mixed family; Zplus is125's complete
complementary positive-seven sum. No selected-label mass is removed
from an unrelated upper bound. All omissions occur inside(AS2).
Then the entire weighted omitted contribution is at most

    B+P3*(E5+kappa*E15+E5d+kappa*E15d)
              +P5*E3+(P3+P5+P1+Pc)*omega.        (AS5)

In particular(AS4) includes the source discrepancy in the pure5
tail; it must not be dropped when converting its error to an E3
price. This source term and124's X arise in different integrals,
the tail and the bounded mean correction respectively.

## 3. One original head and seven residual coordinates

Write124's affine additional mean credit for head b as

    A_b-X_b-L27_b*E27-Lge4_b*Ege4
                    -M5_b*E5d-kappa*M15_b*E15d,
    E3=E27+Ege4.                                 (AS6)

Let C_b(theta,q) be116's finite upper for the same original head,
including its own independent shallow positive-seven labels. Let
a0 be the constant cost coefficient, S the actual survivor mass,
and Ma=116(F5) the bounded transfer price. Ma is not the supremum
M appearing inside124's head argument.

The complete cost is bounded by a0*S+C_b, plus(AS5), minus a1
times(AS6), and plus Ma*omega. We use the affine credit in(AS6)
even if it is negative; this is a valid lower bound for the actual
credit. It retains convexity that clipping need not preserve.

Use117's actual positive packing prices g5,g15. Write

    E5=r/5+x5, E15=r1/5+x15,
    x5>=g5*q5, x15>=g15*q15,
    e0=rho-(r+r1)/5,
    e(q)=e0-g5*q5-g15*q15>=0.                    (AS7)

The seven remaining nonnegative coordinates, in a fixed order, are

    y=(x5-g5*q5, x15-g15*q15, E27, Ege4,
                                           E5d, E15d, omega),
    sum_j y_j<=e(q).                             (AS8)

No extra E3 or family-specific copy of rho is present. The prices
of these coordinates in the complete same-head cost are

    lambda_b=(P3,
              kappa*P3,
              P5+a1*L27_b,
              P5+a1*Lge4_b,
              P3+a1*M5_b,
              kappa*P3+a1*kappa*M15_b,
              Ma+P3+P5+P1+Pc).                  (AS9)

Define the head-independent part

    D_cost(q)=a0*S+B+P3*(r+kappa*r1)/5
                           +P3*g5*q5+kappa*P3*g15*q15,
    H_b(q)=C_b(theta,q)-a1*(A_b-X_b).

All lambda entries are nonnegative. Maximizing their linear
combination on the simplex(AS8) therefore gives the complete upper

    D_cost(q)+max_b[H_b(q)+e(q)*max_j lambda_(b,j)]. (AS10)

Discarding additional individual capacity caps only enlarges this
simplex, so(AS10) remains valid. The constant mass term is actual
a0*S. If S is recovered from the residual, the exact identity is
S=s-T+rho; a saturated face mass cannot replace it off face.

## 4. Multiple costs use one coordinate, without head-tuple enumeration

Let f index costs with nonnegative outer weights beta_f. Their
original test heads may differ, but they share the actual source,
q, rho and all seven coordinates in(AS8). The support cuts may
differ between costs if each choice is fixed for the optimization.

For a tuple of original heads(b_f), its optimal residual payment is

    e(q)*max_j sum_f beta_f*lambda_(f,b_f,j).

Since the maxima are finite, interchange the maximum over head
tuples with the seven-coordinate maximum. For fixed j the head
choices separate by cost. The complete weighted upper becomes

    U(q)=sum_f beta_f*D_f(q)
          +max_j sum_f beta_f*max_b
                          [H_(f,b)(q)+e(q)*lambda_(f,b,j)].   (AS11)

This is an exact identity for the stated affine-support simplex
relaxation. Its seven alternatives refer to one common residual
coordinate. Replacing the second line by

    sum_f beta_f*max_b[H_(f,b)(q)+e(q)*max_j lambda_(f,b,j)]

is an upper bound but can lose the shared-budget information.
Similarly, each cost must retain its own mean credit on the same
head whose finite C_b it uses; a separately maximized credit cannot
be subtracted from another head.

For fixed source, cuts and j, the lambda values and A_b-X_b do
not depend on q. Each H_b is convex by116, and e(q)*lambda is
affine. Positive weighted sums and finite maxima preserve convexity.
Therefore U is convex on the one common polygon

    P={0<=q5,q15<=1/5:g5*q5+g15*q15<=e0},
    max_(q in P)U(q)=max_(q in Vertices(P))U(q).   (AS12)

The proof covers the zero-budget and full-box cases as well. There
is no need to enumerate the Cartesian product of all costs' heads:
at each vertex and coordinate j, compute one independent head
maximum per cost. Source parameters still require their own
validated uniform comparison; this theorem does not make their
dependence convex or justify source-vertex enumeration.

## 5. Support selection and finite-cut face intercepts

Different fixed cuts give different valid bounds. One may compute
the entire(AS12) maximum for each selected cut vector and then take
the least result:

    max_q true_cost(q)<=min_cuts max_q U_cuts(q). (AS13)

Taking a pointwise minimum of supports before using a vertex
theorem is invalid: a minimum of convex functions need not be
convex. A concrete complete-geometric example uses

    0<=e<=1/100,
    F(e)=(3/2)*(1/100-e)+G_5(e,1;2).

The N=3 and N=4 supports are respectively

    U3(e)=1/40-e/2, U4(e)=17/1000+e/2.

Their minimum at e=1/125 is21/1000, while its maximum over the
two interval endpoints is only1/50. The latter is not an upper
bound. The valid fixed-support order gives

    min(max U3,max U4)=11/500.                    (AS14)

The example uses a complete geometric series and exact rationals;
no finite-tail approximation creates the interior maximum.

At zero defect a finite cut leaves the explicit intercept B_N*H.
For H>0 and a finite omitted set, that intercept is strictly positive.
Thus fixed finite cuts do not exactly recover125's zero-defect
face constants. Their entire difference is computable and tends
to zero exponentially with the cuts. A separate exact face branch
or the infimum(AS3) recovers zero; it cannot be asserted for a
single finite cut. This is intrinsic: G(e,H)/e grows without bound
as e tends to zero, so no finite-slope affine upper through the
origin covers all small e when H>0.

Clipping the affine mean credit likewise introduces the negative
of a maximum of affine functions. It must not be declared convex
in the residual. Using(AS6), or a separately fixed valid support
whose full maximum is taken before minimization, avoids that issue.

## Exact executable interface and verification

[shared_budget_affine_tail.py](../../frontier/source-budgets/shared_budget_affine_tail.py)
exports `punctured_support`, `tail_affine`, `branch_affine`,
`evaluate_branch` and `shared_coordinate_upper`. The last function
takes each cost's list of pairs consisting of its same-head affine
data and finite C_b at the same q. It preserves one common seven
coordinate choice and one common polygon point.

The [certificate](../../certificates/source_norms/source-budgets/shared_budget_affine_tail.json)
includes864 complete punctured-support checks and72 exact crossing
equalities, the explicit support-order counterexample, and regressions
using two existing original AP costs on126's face and genuine finite
height5/height8 source families. All six weighted tail comparisons
pass; the four positive-defect tail comparisons have zero support
gap, while the face comparisons retain their explicit finite-cut gap.

The regression also checks48 complete same-head cost inequalities,
15 exact equalities between(AS11) and the brute independent-head
tuple calculation, and six polygon Jensen inequalities. It uses
eight selected original heads per cost to test the interface;
these numerical head maxima are not reported as exhaustive original
head bounds. In these fixtures the common and separately maximized
residual payments coincide, so no numerical improvement is claimed
from sharing alone. The general identity is the argument in section4.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/source-budgets/shared_budget_affine_tail.py --check
```

All original infinite exponent tails remain in the formulas. A
consumer must still maximize over every required original head and
control the complete source domain before reporting a new global K.
