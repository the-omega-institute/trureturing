# A common pair survivor law closes the outside-square slice

Let P={3,5,7,11,13,17,19} and V={7,11,13,17,19}. Consider a finite
family of pairwise distinct odd numerical moduli greater than one,
supported on P together with23,29,31. Every residue is arbitrary and
globally fixed. Pure powers and all originals touching23,29 or31 are
unrestricted. Require each mixed P-supported original m to satisfy

    some exponent of m is at least3, or
    v_3(m)<=1 and v_5(m)<=1.                         (PS1)

Then the complete survivor satisfies

    H(U)>=1466411327218629/18129879040000000000
         >1/12500.                                  (PS2)

This adds all eighty labels3^a5^b q^2 r, a,b in{0,1}, q!=r in V,
to the family of
[Report595](595-outside-square-extension-leaves-an-eighty-label-pair-core.md).
It retains that report's entire749-label extension. On the slice with
central exponents at most one, no outside-square exclusion remains.
Original and query heights are unbounded. The same result transports
to any ten ordered odd primes with the same coordinate roles.

Mixed core originals with maximum exponent two and a squared3 or5
remain outside PS1. In particular this does not combine the result
with [Report596](596-a-six-leaf-boundary-admits-the-central-square-label63.md)'s
separate63 extension. Arbitrary further prime support is not covered.
This is an ordinary proof and a complete integer certificate, not new
Lean verification or a resolution of unrestricted Erdős #7.

## 1. Ten pair unions on the existing actual source

Reuse Report594's product pure-survivor source rho, central3/5 cell
c=(i,j), and five actual thinned star blocks. Write f_q(c) for actual
block survival before thinning and b_q(c) for its conservative factor.
Then

    0<b_q<=f_q,   b_q>=bmin_q=1-3r_q-2a_q,
    r_q=1/(q-1), a_q=1/[q(q-2)],
    rho<=D H_P, D=3458/405.                          (PS3)

At a fixed surviving central cell the actual conditional law is

    nu_c=product_q [chi_q rho_q/f_q(c)].              (PS4)

The old thinned cell mass is its central weight times product_q b_q.
Thus nu_c is a product law even though the full measure, mixing
central cells, need not be a product law.

For each unordered pair e={q,r} in V, group the actual originals

    3^a5^b qr, 3^a5^b q^2r, 3^a5^b qr^2,
    a,b in{0,1},                                    (PS5)

into their union E_e at c. These ten events have ordinary dependency
graph L(K5): events on disjoint pairs depend on disjoint coordinates.
They are unions, not canonical single assignments. No laminar
conflict-graph or resampling-oracle assumption is used.

Put

    kappa_e=r_q r_r+a_q r_r+r_q a_r.

Each of the three outside exponent patterns has a central activation
profile1+row+column+point, weighted by its displayed cap. Retain the
actual row, column or point when its original is active. For absent
or source-null slots choose fixed activation roles only to enlarge
the cap. In particular the three noncentral cap terms remain even
when their originals are absent. Their sum beta_e(c) satisfies

    kappa_e<=beta_e(c)<=4kappa_e,
    nu_c(E_e)<=beta_e(c)/(f_q f_r)
              <=u_e(c)=beta_e(c)/(b_q b_r).          (PS6)

The lower bound on beta is a property of this padded upper estimate.
It does not assert that an absent original actually exists. All actual
events and phases remain fixed.

## 2. A strict Shearer region for every cell and comparison template

Independent sets in L(K5) are matchings in K5, of size at most two.
Its signed polynomial on any induced edge set A is therefore

    Z_A(u)=1-sum_(e in A)u_e
              +sum_(e,f in A, e disjoint f)u_e u_f, (PS7)

where unordered disjoint pairs are counted once. Define

    pmax_e=4kappa_e/(bmin_q bmin_r).

Exact rational evaluation gives

    Z_all(pmax)=851826382717/13419739162053>3/50,
    max_e sum_(f disjoint e)pmax_f
      =45428404/79049907<3/5.                        (PS8)

Every induced polynomial has coordinate derivative
-1+sum_(available disjoint f)u_f<-2/5 throughout the box0<=u<=pmax.
Zeroing omitted coordinates can only increase it. Thus every induced
polynomial is strictly positive throughout the box, as also checked
independently for all1024 induced subsets. Checking only the full
polynomial would not suffice without this argument.

## 3. Query ratios on one actual conditional survivor law

Let F_c be avoidance of the ten actual pair unions. Ordinary
Scott--Sokal conditional avoidance gives

    nu_c(F_c)>=Z_all(u)>0,
    mu_c=nu_c(. | F_c).                              (PS9)

For any query cylinder A with outside support T, it also gives

    mu_c(A)<=nu_c(A) Z_{edges in V\T}(u)/Z_all(u).   (PS10)

For completeness, use the rare-query proof of
[Chapter24, Section3](../../problem-details/24-laminar-prefix-conflicts-under-actual-conditioning.md#3-the-actual-survivor-query-ratio),
with the ordinary shared-coordinate graph here. Add an independent
Bernoulli(epsilon) coin and the event A intersect{coin=1}. Its
nonneighbors are exactly the old pairs outside T; ordinary product
independence verifies the enlarged dependency condition for all events.
Each enlarged induced polynomial is

    Z_B(u)-epsilon nu_c(A) Z_{B minus N(A)}(u).

Finitely many strict old inequalities permit a positive sufficiently
small epsilon. Conditional avoidance for the new event then yields
PS10 by cancelling epsilon. The coin is only a proof device: every
query uses the same mu_c in PS9.

Define the conditional submeasure eta_c=Z_all(u) mu_c. By PS9,
eta_c<=nu_c, and its mass is exactly Z_all(u). Multiply by the old
thinned cell mass and mix central cells. This gives one actual
submeasure zeta_pair<=zeta<=rho, supported on all retained stars and
all actual pair survivors.

Put G_T(c)=1_(c!=(0,0)) product_(q notin T)b_q(c). Multiplying PS10
by the old cell mass and using the original cylinder caps gives the
query grid

    H_T=G_T-sum_(e disjoint T)beta_e G_{T union e}
        +sum_(e,f disjoint each other and T)
             beta_e beta_f G_{T union e union f}.    (PS11)

The unqueried denominators cancel; factors b_q/f_q at queried
coordinates are at most one. H_empty is the exact chosen mass grid.
All later restrictions only decrease raw query masses. These statements
apply to every query height, not only the first two digits.

## 4. Eliminate pair-phase choices without changing the law

Since PS7 decreases in each coordinate throughout its strict box,
beta_e>=kappa_e gives a uniform upper query grid

    J_T=G_T-sum_(e disjoint T)kappa_e G_{T union e}
        +sum_(e,f disjoint each other and T)
             kappa_e kappa_f G_{T union e union f}.
    0<=H_T<=J_T<=G_T.                               (PS12)

Only query and remaining-original upper bounds use J. It is not
declared to be the actual mass grid.

Let A_T,B_T,C_T,D_T,E_T,F_T be Report594's six screens of G_T.
The central average of the negative single-edge term is at most

    average(beta_e G_e)
      <=kappa_e(A_e+B_e/4+C_e+E_e/4).               (PS13)

Indeed each outside exponent type has one unconditional contribution,
at most one row, one column and one point. Bound their averages by
the corresponding screens, then sum their three weights to kappa_e.
This is an upper bound even if the individual maximizing cells cannot
occur together.

The positive disjoint-pair terms satisfy beta_e beta_f>=kappa_e kappa_f.
Consequently the actual pair-survivor mass is at least

    Mlow=A_empty-sum_e kappa_e(A_e+B_e/4+C_e+E_e/4)
          +sum_(e disjoint f)kappa_e kappa_f A_{e union f}. (PS14)

Each matching leaves one outside coordinate; the fifteen positive
terms can therefore be grouped into five coefficients. PS12 and PS14
are simultaneous bounds for one actual measure, not independently
attained source choices.

## 5. Complete inventory and continuation

The pair stage retains120 distinct numerical labels: forty squarefree
labels already charged in Report594 and eighty new square-pair labels.
Starting with Report595's old loss plus749 extra charges, remove the
forty squarefree charges. Equivalently, start with the old loss plus
all829 formerly remaining outside-square labels and remove all120
PS5 charges. Independent literal label enumeration gives identical
nonnegative remaining-loss coefficients L.

Let S_j(J) be the six screens of PS12, over all32 outside supports,
and retain the entire weighted future-query array W of Report594.
For the actual submeasure eta obtained by avoiding every remaining
original, write s=eta(1). Use the homogeneous convention

    Gamma_Q(eta)=max_b integral[sum_(d|Q)1_([b_d]_d)]^2 d eta,

with one complete query layout b per maximization and the unit label
d=1 included. Thus Gamma_Q(eta/s)=Gamma_Q(eta)/s. Then

    s>=Mlow-sum_j L_j S_j(J),
    Gamma_Q(eta)<=s+sum_j W_j S_j(J)                (PS15)

at every finite resolving height Q. No occupied or unoccupied query
label is removed. With the same through31 controls and
c=1084133/201247200, the direct continuation gate is bounded below by

    Klow=(1-c)Mlow-sum_j[(1-c)L_j+cW_j]S_j(J).      (PS16)

Positivity implies s>0 and a normalized complete query moment below
1/c. The actual capped continuations at23,29,31 are then legal on the
same law. Report595's mass and density calculation gives

    H(U)>=33Klow/(200D).                            (PS17)

## 6. Five-factor concavity and the full integer certificate

For fixed other star factors, G_T and J_T are affine in the remaining
factor: every matching is disjoint, so no factor is repeated. Each
screen is linear or a maximum of linear forms. All coefficients of
subtracted screens in PS14 and PS16 are nonnegative; positive terms
are separately affine. Thus Klow is separately concave in the five
star vectors and in t in[1/3,2/3]. Report594's64-template comparison
and two endpoints remain valid. No enumeration of pair-phase
templates is required.

The global symmetry of the three nonzero central columns gives the
same complete number of comparison cases as before:

    2^10*2*(4^10+3*2^10+2)/6=358963200.             (PS18)

Use dyadic factor intervals at2^20, matching coefficients at2^30,
and outer gain/debit coefficients at10^9. For a query upper bound,
subtract lower enclosures of the negative matching terms and add
upper enclosures of positive matching terms; taking the minimum with
the old G upper bound is permitted by PS12. Positive mass terms use
lower enclosures, and all subtracted screens use upper enclosures.
The absolute signed64 accumulation bound is28442095597387776<2^63.

The full scan covers PS18 exactly and gives

    Klow>=548601319573/131072000000000>0.           (PS19)

The minimizing comparison codes are(9,18,27,27,27), t=2/3. At this
layout the independent exact rational expression is

    100866047917454812695714061/24078552333444213276672000000.

Its difference from the integer lower enclosure is

    341462680102646059861085983/96314209333776853106688000000000>0.

The exact witness confirms the directed computation; the full scan
provides uniformity. Substituting PS19 into PS17 yields PS2.

The [producer](../../frontier/cover-geometry/outside_pair_shearer_profile.py),
[engine](../../frontier/cover-geometry/outside_pair_shearer_scan.cpp) and
[data](../../frontier/cover-geometry/outside_pair_shearer_profile.json)
retain all120 labels, the1024-subset Shearer check, exact coefficients,
source/input fingerprints, complete coverage and rational reconstruction.
All277 producer checks pass. Independent checks reconstruct the
inventory and same-law inequalities; direct calls to the integer
engine on32 layouts agree with an independent integer evaluator,
and all64 endpoint enclosures lie below their exact rational values.
Undefined-behavior sanitizer checks pass on those layout evaluations.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/outside_pair_shearer_profile.py

Finally, Report592's finite-height digit-injection averaging preserves
PS1, every exponent vector and numerical distinctness, so it transports
PS2 to arbitrary ten ordered odd primes. It does not add further prime
coordinates or remove the central-square restriction.
