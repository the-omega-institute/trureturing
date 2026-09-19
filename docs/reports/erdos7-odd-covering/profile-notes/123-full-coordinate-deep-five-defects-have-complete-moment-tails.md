[Index](../marked_head_profile.md) · [Deep-five mean credit](122-two-complete-deep-five-families-transport-the-mean-credit.md) · [Dominated survivor excess](115-a-dominated-defect-controls-complete-independent-label-tails.md) · [Pure3 projection](119-the-complete-pure-three-family-has-one-projected-defect.md) · [Finite source bridge](116-signed-face-duals-transport-one-shared-finite-source.md)

# Full-coordinate deep-five defects have complete moment tails

The two deep-five defects of122 lift to positive measures on the full
old3/5 coordinates. Their masses are controlled by the same existing
capacity defects, and every arbitrary original cylinder has a quantitative
cap. The complete first and second moments of independent descendant-five
loads have exact finite-correction formulas.

For a five-cylinder of depth k>=2, the relevant coefficient is

    A_k=(4*k-3)*5^-k/20.                           (FC1)

For any fixed ternary event T, use H=eta(T) for the deep pure5 defect
and H=eta(T intersect root1) for the deep15 defect. If its corresponding
mass upper is E, each cylinder error is at most min(E,H*A_k).
Let N>=2 be the first index with H*A_N<=E. For E,H>0 the complete
first and second independent-load bounds are

    R1(E,H)=(N-2)*E+H*(2*N-1)*5^-N/8,
    R2(E,H)=(N-2)^2*E
                         +H*(16*N^2-28*N+15)*5^-N/32.         (FC2)

Both bounds are zero if E=0 or H=0. This is an ordinary full-coordinate
defect theorem with exact rational checks. It controls virtual-deletion
errors; it does not identify a complete actual survivor upper, restore
all endpoint cylinder estimates, or prove a new global K.

## 1. Complete every potential ideal label

Use the actual raw source

    0<=Lambda<=eta tensor Haar5,
    h=eta(1), h0=eta(root0), h1=eta(root1)>h0.

The first source ternary root is removed and has zero eta mass. The
complete forbidden cofactor families are5^b*7^e and3*5^b*7^e,
b>=2,e>=1. An absent original label has zero virtual measure. The
complete seven weights satisfy

    u_e=6/(5*7^e), sum_e u_e=1/5,
    sum_(b>=2,e>=1)u_e*5^-b=1/100.                (FC3)

For every potential deep pure5 label choose a depth-b ideal cylinder
F5_(b,e). If the label is present, this must be its actual five residue.
If absent, choose any depth-b cylinder. The ideal is never empty merely
because the original label is absent. Define

    I5=sum_(b,e)u_e*(eta tensor Haar5) restricted to F5_(b,e),
    V5d=sum_(present b,e)u_e*Lambda restricted to actual F_(b,e).

Every present term has the same cylinder in its ideal and actual
measure, so it has a positive difference. Every absent term has a
positive ideal and zero actual term. Thus

    Xi5=I5-V5d>=0,
    I5(1)=h/100, Xi5(1)=E5d=h/100-V5d(1).         (FC4)

For every potential deep15 label put its ideal ternary root at root1.
If the actual label is on root1, its ideal five cylinder must equal
the actual one. For a wrong-root, removed-root or absent label, choose
any depth-b five cylinder. Let I15 be the complete sum of these ideal
copies of eta restricted to root1 tensor Haar5, and let V15correct
retain only the actual labels on root1. Then

    Xi15=I15-V15correct>=0,
    I15(1)=h1/100,
    Xi15(1)=E15d+V15wrong(1)<=kappa*E15d,
    kappa=h1/(h1-h0), E15d=h1/100-V15d(1).        (FC5)

The last inequality is122's labelwise wrong-root capacity payment.
Removed-root and absent labels have zero actual wrong mass and their
full unused capacity. All ideal sums have the finite total masses
in(FC4)--(FC5); monotone convergence defines them over every exponent.

Completing absent labels in both families is necessary for the displayed
exact ideal masses and projections. These copies are bookkeeping
measures, not additional original forbidden congruence classes. Their
arbitrary residues do not change the actual family.

Projecting(FC4)--(FC5) onto the ternary coordinate gives precisely122's
eta/100 and eta restricted to root1 /100 references. In the full
coordinates, the ideal five distribution retains the chosen labelled
cylinders; it is not replaced by Haar5/100.

## 2. Arbitrary independent original cylinders have exact ideal caps

Let T be any measurable ternary event and G a five-cylinder of depth k.
The original test G is independent of every forbidden label. Two
5-adic cylinders of depths b,k are either disjoint or have intersection
of Haar mass5^-max(b,k). Hence, writing H=eta(T),

    I5(T times G)
      <=H*sum_(b>=2,e>=1)u_e*5^-max(b,k).         (FC6)

For k>=2,

    sum_(b>=2)5^-max(b,k)
      =(k-1)*5^-k+5^-k/4
      =(k-3/4)*5^-k.

Multiplying by sum_e u_e=1/5 gives A_k in(FC1). For k=0,1 the same
sum gives A_0=A_1=1/100. In particular A_2=1/100 as well.
Since Xi5<=I5, its global mass and(FC6) give

    Xi5(T times G)<=min(E5d,eta(T)*A_k).          (FC7)

The identical proof for I15, whose ternary support is root1, gives

    Xi15(T times G)
      <=min(kappa*E15d,eta(T intersect root1)*A_k). (FC8)

Any smaller proved actual defect mass can replace the first argument.
The same caps hold for an intersection of finitely many independently
chosen five cylinders, with k their maximum depth, because their
intersection is empty or one depth-k cylinder. No simultaneous
attainment of different intersection caps is assumed.

These are already root/cell-restricted defect bounds: take T to be an
original root, cell, or deeper ternary cylinder. For a depth-a ternary
cylinder, eta(T)<=3^-a. Thus(FC7)--(FC8) include errors on the selected
25,27,75,81 events. For27 and81, k=0 gives the raw upper factors1/2700
and1/8100 before taking the minimum with E. This statement concerns
the two defects, not the mass of actual survivors on those events.

## 3. Complete independent-load moments

Let the original descendant-five tests be

    L_i=sum_(k>=2)1_(G_(i,k)), i=1,...,m,

where every residue may vary with both i and k. Tests may have missing
labels, which only decreases these nonnegative expressions. Let Xi
denote either full-coordinate defect, and set E,H as in(FC7) or(FC8).
Expand finite partial loads inside a fixed T. A tuple of m exponent
indices with maximum k occurs

    D_m(k)=(k-1)^m-(k-2)^m

times. The joint cylinder has Xi mass at most min(E,H*A_k). Therefore

    integral_(T) product_(i=1..m)L_i dXi
      <=R_m(E,H),
    R_m(E,H)=sum_(k>=2)D_m(k)*min(E,H*A_k).        (FC9)

Monotone convergence removes all truncations. Since A_k decays
geometrically times a linear factor, the complete sum converges for
every fixed positive integer m. The first and second formulas in(FC2)
are implemented; higher m in(FC9) remain an ordinary general interface.
The m=2 statement permits different original tests. In particular it
also bounds L squared, without equating independently labelled loads.

The sequence A_k is decreasing for k>=2 and tends to zero. If E,H>0,
the crossing N in(FC2) is finite. The contribution before N is exactly

    E*sum_(k=2..N-1)D_m(k)=E*(N-2)^m.             (FC10)

For the rest, exact polynomial-geometric summation gives

    sum_(k>=N)A_k=(2*N-1)*5^-N/8,
    sum_(k>=N)(2*k-3)*A_k
                         =(16*N^2-28*N+15)*5^-N/32.           (FC11)

Equations(FC10)--(FC11) prove(FC2), including every remaining label.
The complete ceilings are

    R1(E,H)<=3*H/200,
    R2(E,H)<=23*H/800.                            (FC12)

Equivalently, subtract the finite correction for k<N from these full
geometric ceilings:

    R_m(E,H)=H*sum_(k>=2)D_m(k)*A_k
                         -sum_(k=2..N-1)D_m(k)*(H*A_k-E).     (FC13)

The helper checks both evaluations independently. As E decreases to
zero, each complete R_m tends to zero by dominated convergence. There
is no arbitrary error atom and no finite exponent cutoff in these
formulas. No uniform linear price R_m(E,H)<=C*E is claimed.

## 4. Keep the same actual capacity allocation

The raw complete capacities h/100 and h1/100 are the deep portions
of85's h/20 and h1/20 families, after their shallow h/25 and h1/25
portions. Thus122's shared allocation remains

    E5+E15+E3+E5d+E15d+omega<=rho.               (FC14)

With117's proved packing prices this gives

    G5*q5+G15*q15+E3+E5d+E15d+omega
                                      <=rho-(r+r1)/5.        (FC15)

The full-coordinate construction introduces no additional defect
coordinate. In particular kappa*E15d is an upper bound for the mass
of Xi15, not another nonnegative summand that can be added to(FC14).
The E27 and selected E_D variables are subfamily parts of E3, as
explained in120; they cannot be added as disjoint budgets either.

For a fixed source, any combination of the first or second defect
moments must use the same E5d,E15d and the same original test head as
its finite contribution. One cannot give the full remaining rho to
each family or cost independently and then claim the stronger shared
optimization. Such independent maxima are at most a deliberately
weakened upper bound, with their loss of compatibility stated.

The bounded mean credit of122 can still use its affine defect prices.
For example, on sigma<=1/27, its M5<=2 and kappa*M15<=322/79<5.
Since116's M_a>=5*a1, these two mean-credit prices fit within that
existing M_a price on the common residual. This observation does not
turn the nonlinear full-tail errors in(FC9) into affine payments.

## 5. Complete tails defeat a blanket vertex argument

For fixed H, every R_m(E,H) is increasing and concave in E, because
it is a positive sum of min(E,H*A_k). Adding it to a convex finite
objective does not in general preserve convexity.

There is an exact counterexample using this first-moment function
itself. Put H=1, q+E=1/100 and maximize

    (3/2)*q+R1(E,1).

At both endpoints E=0 and E=1/100 the value is3/200. At the feasible
interior point

    E=9/2500, q=4/625,

the value is91/5000, strictly larger. This is a counterexample to
the proposed optimization shortcut; it is not a covering construction.

Two safe uses are to bound each full tail uniformly before applying
116's finite q-polygon argument, or to fix the relevant defect masses,
optimize the convex finite q part conditionally, and certify the remaining
defect-mass optimization separately. Shared allocation(FC15) must be
retained in either case.

## 6. What this supplies and what the survivor transport still needs

Profile115 constructs a positive survivor excess dominated by raw
Haar, provided its reference is positive. Profile119 supplies a
special pure3 five projection and a positive reference for the actual
global five marginal. Profile122 only needed the ternary projections
of the two deep-five defects to recover its mean-head credit. This
note supplies their full-coordinate measures, arbitrary root/cell
cylinder caps and complete independent first/second moment errors.

The two Xi measures here are not asserted to be bounded by a fixed
multiple of Haar. An ideal family may concentrate its independent
cylinders along one nested sequence, producing the k factor in A_k.
Replacing A_k by a constant times5^-k without proof would remove
precisely the full-coordinate information retained here.

To obtain an actual survivor comparison one may retain the virtual
families in the identity with the single error V-delta, schematically

    mu<=w*Lambda-I5-I15+Xi5+Xi15+(V-delta),        (FC16)

with other proved virtual deletions retained as appropriate. The
following obligations remain for a full72/75/98/109 transport:

* Control the same actual ideal-reference term for each original
  root/cell-restricted descendant test. Its five-coordinate intersections
  are not determined by the projections eta/100 and eta(root1)/100.
* Establish positivity of the chosen survivor reference, or explicitly
  account for clipping. The signed measure w*Lambda-I5-I15 need not
  be positive off face, so115's domination of its positive excess by
  mu cannot be applied to that expression without an additional step.
* Insert119/120's pure3 information and the separately proved forced27
  cell geometry into the same original-cylinder estimates. Defect bounds
  alone do not identify where the actual ideal deletion occurs.
* Consume all complete tail errors and finite head credits using(FC15),
  including the existing positive-seven and selected25/27/75/81 terms.
  The optimized full numerator and a new global comparison remain open.

One valid positive-part construction is to replace a signed reference
J by J_+ before defining a survivor excess. From mu<=J+epsilon one
gets mu<=J_++epsilon and (mu-J_+)_+<=mu. But estimating J_+ is then
a new reference-cost obligation; this observation does not license
using the old un-clipped endpoint constants.

## Reproduction and scope

Run

    python3 -I -O docs/reports/erdos7-odd-covering/frontier/deep_five_full_coordinate_defect.py --check

The helper exports cylinder_coefficient, cylinder_bound, moment_tail
and complete_moment. Its certificate uses five actual finite original
cofactor configurations: aligned, wrong root, mixed roots, intersecting
source cylinders and absent labels. All remaining ideal b/e labels are
included by exact geometric sums before projection onto the finite grid.
The exact original source mask is checked independently.

It checks positivity of the full-coordinate differences, both exact mass
identities, independent ternary/five cylinder caps, complete first/second
moment formulas and the interior-budget counterexample. Finite masks
and test loads validate the implementation; the ordinary measure and
monotone-convergence proofs above establish the unrestricted exponent
statements. No Lean verification or new unrestricted Erdős#7 result is
claimed.
