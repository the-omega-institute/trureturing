# A six-leaf boundary admits the central-square label63

Let P={3,5,7,11,13,17,19} and V={7,11,13,17,19}. Consider any
finite family of pairwise distinct odd numerical moduli greater than one,
supported on P together with23,29. Every original residue is arbitrary
and globally fixed. Permit all pure powers, all squarefree mixed
P-supported originals, all mixed P-supported originals with some
exponent at least three, all ten labels3q^2,5q^2 for q in V, and the
additional numerical label63=3^2*7. Every original touching23 or29 is
unrestricted. The complete survivor has Haar density

    H(U)>=3969/426025600>1/108000.                    (CS1)

The same lower bound holds for any nine ordered odd primes, preserving
all exponent vectors and the first-seven/last-two roles. The additional
label then becomes r_1^2 r_3, for target primes r_1<...<r_9.
There is no cutoff on original or query heights. This extends the
nine-prime family of
[Report594](594-five-joint-blocks-admit-ten-mixed-square-labels.md)
by a central-square original. The result does not combine63 with
[Report595](595-outside-square-extension-leaves-an-eighty-label-pair-core.md)'s
749-label extension, or with the unrestricted31 coordinate. It is an
ordinary proof with a complete integer branch certificate, not a new
Lean result or a resolution of unrestricted Erdős #7.

## 1. Refine the actual ternary source before taking comparison states

Use the single product source rho of Reports591 and594. At3 it is
normalized Haar on the complete actual pure survivor in two retained
first roots. If the pure3 original is absent, an auxiliary first-root
deletion only restricts support. The remaining pure originals have
total Haar mass at most sum_(e>=2)3^(-e)=1/6, so the surviving Haar
mass in the two roots is at least1/2. Consequently rho_3 has density
at most2. Refine the roots into their six mod9 children and write

    w_l=rho_3(child l),   sum_l w_l=1,
    0<=w_l<=2/9,         l=0,...,5.                 (CS2)

Every depth-e ternary cylinder has mass at most2*3^(-e). In particular,
the complete depth-at-least-three sum is at most1/9. These are bounds
on one actual pure-survivor law; a query never selects a new normalizer.
The other coordinates and the complete source density are unchanged:

    r_q=1/(q-1),  a_q=1/[q(q-2)],
    rho<=D H_P,  D=3458/405.                        (CS3)

Write i(l)=floor(l/3), and let j range over the four retained5-roots.
The central15 deletion is the cell(i,j)=(0,0). For each q retain the
actual block3q,5q,15q,3q^2,5q^2; for q=7 also retain63. Its ternary
phase selects one mod9 leaf l*. Missing or source-null slots can be
filled by fixed auxiliary restrictions, as in Report594. Every active
original keeps its original phase.

Conditional q-block survival f_q(l,j) is bounded below by

    b_q(l,j)=1-r_q[1_(i=R_q)+1_(j=C_q)+1_((i,j)=K_q)]
               -a_q[1_(i=R'_q)+1_(j=C'_q)]
               -1_(q=7)r_7 1_(l=l*).              (CS4)

The additional term uses the actual63 leaf and its q-first-root cap.
For q=7 the lower bound is at least29/105; all other factors are at
least31/70. Thus theta_q=b_q/f_q lies in[0,1]. Define

    d zeta=1_((i,j)!=(0,0)) product_q(chi_q theta_q) d rho,
    eta=1_(complete actual P-survivor) zeta.         (CS5)

Here chi_q is the actual block-survival indicator. Given a central
leaf and5-root, the q-coordinates are independent, so integrating each
factor chi_q theta_q gives exactly b_q. In particular

    eta<=zeta<=rho<=D H_P.

This constructs the supported law before any convex comparison or
query maximization.

## 2. Eight query screens retain the newly exposed second digit

For an outside-prime support T subset V, drop both chi_q and theta_q
at q in T when bounding a query or a remaining original. They lie in
[0,1], so the result is an upper bound on the same actual measure.
Integrating the other coordinates leaves

    g_T(l,j)=1_((i(l),j)!=(0,0)) product_(q notin T)b_q(l,j).

Put h_l=(1/4)sum_j g_T(l,j). The eight screens are

| Ternary query height | No5 coordinate | With5 coordinate |
| --- | --- | --- |
|Absent|A_T=sum_l w_l h_l|B_T=max_j sum_l w_l g_T(l,j)|
|One|C_T=max_i sum_(i(l)=i)w_l h_l|D_T=max_(i,j)sum_(i(l)=i)w_l g_T(l,j)|
|Two|E_T=max_l w_l h_l|F_T=max_(l,j)w_l g_T(l,j)|
|All heights at least three|H_T=(1/9)max_l h_l|I_T=(1/9)max_(l,j)g_T(l,j)|

For the last row, maximizing over all six leaves is a conservative
upper bound, including leaves of actual mass zero. The5-coordinate
and outside-coordinate caps multiply these screens.

For any nonternary support J, define the complete, below-three and
squarefree coefficient sums

    u_J=product_(p in J)1/(p-2),
    v_J=product_(p in J)[1/(p-2)-1/(p(p-1)(p-2))],
    z_J=product_(p in J)1/(p-1).                    (CS6)

These are exact infinite geometric sums. For mixed originals without3,
the height-three charge is u_J-v_J. For ternary heights one and two,
the nonternary charge is also u_J-v_J; at ternary heights at least
three it is u_J. Squarefree original charges use z_J only in the
absent/first-height rows, excluding the retained3q,5q,15q labels.
These loss rules apply only to mixed supports: without3 require
|J|>=2, and with3 require J nonempty. Every pure support has zero
remaining original loss, while all three query-height groups for
the pure support{3} remain included.
Pure originals have already been imposed. The new63 original and the
ten3q^2,5q^2 originals are handled in CS5 and receive no further debit.

Every nonunit query, including all retained original labels, remains
in the query inventory. Summing CS6 in the eight modes and32 supports
gives nonnegative256-entry loss and query arrays L,Q. If a=A_empty,
then, with G=566/49,

    eta(1)>=a-L,
    R_P(eta)<=Q,
    G eta(1)-R_P(eta)>=G(a-L)-Q.                   (CS7)

The producer independently reconstructs these arrays by summing all
127 nonempty supports. No finite height substitutes for the complete
series.

## 3. Concavity gives five local templates and sixteen source states

For each q, choose a row from R_q,R'_q and a column from C_q,C'_q,
independently, with weights r_q/(r_q+a_q),a_q/(r_q+a_q). Equation CS4
is the average of the64 templates

    1-(r_q+a_q)[1_(i=I_q)+1_(j=J_q)]
      -r_q 1_((i,j)=K_q)-1_(q=7)r_7 1_(l=l*).    (CS8)

For fixed other factors, a is linear in the remaining factor. Each
screen is linear or a maximum of linear forms, and each debit
coefficient is nonnegative. Thus the right side of CS7 is separately
concave in each q-factor. Successively taking comparison vertices
reduces to the64 templates at each of five primes. Comparison
templates need not themselves be actual simultaneous original phases;
they are not substituted for the source CS5.

The gate is also concave in w, since its deep screens are independent
of w. The polytope CS2 has exactly30 vertices: the permutations of

    (0,1,2,2,2,2)/9.                               (CS9)

Indeed a vertex has at most one coordinate strictly between0 and2/9;
the sum constraint forces four entries2/9, one1/9 and one0.
Within each root the unmarked leaf grids coincide, and the marked
grid is no greater. At any CS9 vertex there is a live unmarked leaf
in each root. Hence the maximum over all leaves in H_T,I_T equals
the maximum over live leaves at these comparison vertices.

After permutations of the unmarked leaves, the marked root needs only
its total weight, marked weight and largest unmarked weight. In units
of1/9, these triples are

    (3,0,2),(3,1,2),(3,2,1),(4,0,2),
    (4,2,2),(5,1,2),(5,2,2),(6,2,2).

The other root has total9 minus the first total and largest leaf
weight2. Marking either root yields16 states. This relaxation includes
sources with no pure9 deletion; it does not assign them an artificial
actual density of2.

## 4. A complete branch certificate

Column0 is fixed by the central15 deletion. Permuting columns1,2,3
preserves all factors, screens and source states. Restricted-growth
names for the ten column fields give one representative per orbit.
Burnside's formula gives

    layout_orbits=2^10*(4^10+3*2^10+2)/6=179481600,
    source_state_cases=16*layout_orbits=2871705600.  (CS10)

The engine encloses factors and products in dyadic intervals of scale
2^20. It rounds the positive gain down and all debit coefficients up
at scale10^8. Every screen has common denominator36*2^20.

For an assigned prefix of d factors, all remaining factors are at
most one. Omitting them therefore bounds every debit screen above.
The positive mass is bounded below by its assigned-factor lower
bound times

    beta_d=product_(q still unassigned)(1-3r_q-2a_q).

The7-block, which contains the additional63 debit, is assigned before
any branch can be certified. The remaining beta_d is therefore valid.
Rounding beta_d down and taking a final lower integer quotient
preserve the mass lower bound. Indistinguishable remaining query
masks have their nonnegative coefficients summed.

A partial branch with lower bound at least1/1000 certifies all its
completions; otherwise the engine expands it. Suffix counts are
checked against an independent restricted-growth recurrence. The
actual rounded-array bound on the absolute signed64 accumulation is

    (rounded_gain+sum rounded_coefficients)*36*2^20
      =138945702427361280<2^63.                    (CS11)

The complete traversal certifies all2871705600 cases, with no failing
leaf. Its smallest certified branch lower bound is

    3774909371007/3774873600000000>1/1000.           (CS12)

This is a uniform certificate, not the exact global minimum: positive
partial branches are not expanded. The exact reference layout with
codes(9,27,27,27,27), weights(2,2,2;2,0,1)/9 and marked leaf3 has gate

    502837644894249281/27990252498368160000.

The reference layout checks the implementation; CS10--CS12 supply
global coverage. Independent rational reconstruction checks the
256-mode and127-support evaluations, all16 source states and directed
integer enclosures. The producer also checks malformed inputs and
requires full case coverage, rather than accepting an exit code alone.

## 5. Continue through23 and29 on the same law

Report591's raw continuation takes any actual supported submeasure
with G eta(1)-R_P(eta)>=delta and density at mostD H_P to Haar survivor
at least49delta/(616D). Using delta=1/1000 in CS7 and CS12 yields

    H(U)>=49/(1000*616*D)=3969/426025600,

which is CS1. The argument permits dead old fibres and keeps all
original phases and every future query on the one constructed law.

For the ordered-prime extension, apply Report592's digit-injection
averaging at a finite resolution containing every original. A target
original pulls back to either no cylinder or one source cylinder with
the same complete exponent vector. Distinct numerical labels remain
distinct, and the additional vector(2,0,1,0,0,0,0) remains in the
allowed inventory. Every injection therefore leaves source survivor
at least CS1. Averaging uniformly shifted injections gives target
Haar and the same lower bound. This does not identify different prime
rings or assume that the six-leaf kernel is unchanged at larger primes.

There is a specific limitation to appending31 with the current
weighted envelope. Ternary height groups one,two,at-least-three have
query weights3,5,8, respectively. At the reference layout above, put

    s_0=803492421556973483/4569837142590720000,
    Wbar=4842375295428315876809/146234788562903040000,
    c=1084133/201247200.

Then the existing through31 sufficient gate is

    (1-c)s_0-c Wbar
      =-983186847955838985086629/280279445151202482585600000<0.

This is a failure of that upper-envelope certificate. It is neither
an actual covering nor a lower bound excluding every survivor law.
It does not justify combining CS1 with Report595's separate extension.

The [producer](../../frontier/cover-geometry/central_square_63_profile.py),
[engine](../../frontier/cover-geometry/central_square_63_scan.cpp) and
[data](../../frontier/cover-geometry/central_square_63_profile.json)
retain the generated coefficients and factors, source states, exact
reconstructions, arithmetic bounds, complete coverage and source
fingerprints. Reproduce with

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/central_square_63_profile.py
