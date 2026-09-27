# Two outside prime groups preserve the finite-template separator

Let P={3,5,7,11,13,17,19}. Let R,S be disjoint finite sets of primes,
both disjoint from P, such that

    alpha_R=product_(r in R) r/(r-1)-1<=1/22,
    alpha_S=product_(s in S) s/(s-1)-1<=1/28.             (G1)

Empty groups are allowed. Take any finite family of congruence classes
with pairwise distinct odd numerical moduli greater than1, supported on
P union R union S. Old-only classes are arbitrary. Each later modulus has
its unique numerical decomposition m_i=d_i*n_Ri*n_Si, n_Ri*n_Si>1.

Choose p in{7,11,13,17,19} and prescribe the finite templates of
[report518](518-finite-prefix-templates-allow-arbitrary-old-residue-tails.md):
two prefixes A_q,B_q with different first digits at q=3,5,p, of respective
depths11,7,6, and one common depth4 prefix C_q at each remaining old q.
For every complete original later label choose one fixed sigma_i in{A,B}
such that, simultaneously at3,5,p,

    a_i=sigma_(i,q) modulo q^min(v_q(d_i),h_q),

and at the other old coordinates

    a_i=C_q modulo q^min(v_q(d_i),4).                    (G2)

The selector is fixed for the whole numerical modulus across every
tested point and estimate; it is not chosen separately by coordinate.
All deeper old residues and all outside residues may vary arbitrarily
per label. There is no bound on the finite exponents or number of labels.

Under G1--G2, the family does not cover the integers. Its actual completed
old source gives mass greater than1/20000 to old points with positive
later-fibre survival. The number of outside primes need not have any
fixed upper bound, provided the two finite groups satisfy G1.

In particular, this extends report518 from the outside pair23,29 to any
two distinct primes r>=23,s>=29. The proof retains each actual numerical
modulus and proves inclusion of its deletion quantities in the same
numerical budget model. It does not replace smooth cofactors by powers
of synthetic primes or identify different original moduli.

## The numerical budget depends on reciprocal inventory

First consider the comparison family with two full global old
references, split at3,5,p and common at the other four old coordinates.
For finitely many tested old points i, let A_i,B_i be their old numerical
divisor boxes, including d=1. For nonnegative weights w_i set

    N(w)=sum_d max(sum_i w_i 1_Ai(d),sum_i w_i 1_Bi(d)). (G3)

At each fixed actual pair(n_R,n_S), the weighted number of active old
labels is bounded by N(w). Distinct numerical moduli give at most one
class per d*n_R*n_S, and that class uses one of the two complete masks.
The same actual selectors supply all inequalities in w; separate maxima
are upper bounds and need not be jointly attained.

Use normalized product Haar H_R,H_S on the two disjoint outside groups.
In fibre i let a_i be the H_R mass deleted by pure-R classes, b_i the H_S
mass deleted by pure-S classes, and c_i the actual additional H_R times
H_S mass deleted by the mixed union inside the pure-surviving product.
This c_i is a union mass, bounded by the sum of possibly overlapping
mixed-cylinder masses. Put

    t_i=22a_i, u_i=28b_i, y_i=616c_i.

A group cylinder of numerical modulus n_R has Haar mass1/n_R. Finite
Euler products give

    sum_(n_R>1, supp(n_R) subset R) 1/n_R=alpha_R,

including every exponent; similarly for S. Weighted union bounds yield

    w dot t<=22alpha_R N(w)<=N(w),
    w dot u<=28alpha_S N(w)<=N(w),
    w dot y<=616alpha_R alpha_S N(w)<=N(w).              (G4)

Also0<=t_i<=22, 0<=u_i<=28 and y_i>=0. Each pure-surviving set lies
within one coordinate group; the two groups are independent under full
product Haar. Their internal primes need not have independent survivor
events. For the final actual later survival fraction s_i, exactly

    (22-t_i)(28-u_i)-y_i=616s_i.                         (G5)

These are all the relaxed deletion premises used by the retained
two-axis row model. No independence of old points, actual conditional
source coordinates or mixed phases has been assumed.

## All geometric rows retain their meaning

The finite row model in
[report509](509-finite-height-zero-edges-strengthen-the-global-support-bound.md)
has the following dependence on G3--G5:

| Row or cutoff | Sufficient unchanged input |
| --- | --- |
| Ordinary pair | Individual and joint axis and mixed bounds; clipped pair minimum at least1/3 |
| Genuine triple | Common N(w) inequalities and minimum of sum_i w_i(22-t_i)(28-u_i)-N(w) at least sum(w)/6 |
| Genuine four-point edge | The same two capped axis polytopes and mixed polytope; R-y=616s |
| Binary triangle clique | Three constituent pair exclusions for one binary support |
| Upward order | Inclusion of both old-label boxes for each original label |
| Safe Q<=19 profile | s>=(1-19/22)(1-19/28)-19/616=1/77 |

The pair bound is the numerical theorem of
[report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md).
The weighted triple bounds are those of
[reports499](499-weighted-mixed-budgets-exclude-old-zero-triples.md)
and [501](501-complete-weighted-boundaries-cut-a-binary-obstruction.md).
The joint four-point certificate in
[report505](505-joint-four-point-budgets-exclude-what-no-fixed-weight-can.md)
excludes its101-direction domain using the same rational branch tree.
Each consumes the actual tuple through G4--G5, with no23/29 phase identity.
All ordinary rows therefore remain valid for strict s<theta0, where
theta0=1/3696, and hence for exact-zero survival.

Old-box inclusion remains valid because the same label keeps its selector
and entire outside cylinder as the old boxes enlarge. The signed loads
of order rows, complete Q>=39 overflow and old reference weights are
unchanged. Binary clique inequalities still require binary support;
they are not assertions about arbitrary fractional supports.

The remaining qualitative pair requires finiteness. For individual old
inventories at most21,26 and common-selector inventory at most35,
[report506](506-finite-height-pair-excludes-zero-support-at-a-closed-boundary.md)
proves from the closed axis constraints

    (22-t_x)(28-u_x)+(22-t_y)(28-u_y)>=35.               (G6)

Its four-corner calculation has minimum35. G4 puts the grouped tuple
inside that same closed domain.

Choose finite cutoffs J_l>=1 bounding all original outside exponents,
and define

    alpha_R(J)=product_(r in R) sum_(e=0..J_r) r^(-e)-1,
    alpha_S(J)=product_(s in S) sum_(e=0..J_s) s^(-e)-1,
    kappa_J=616alpha_R(J)alpha_S(J).

The actual finite mixed inventory gives y_x+y_y<=35kappa_J. If both
groups are nonempty, each finite sum is strictly below its complete
Euler product, so kappa_J<616alpha_R alpha_S<=1. If either group is
empty, kappa_J=0<1. Thus in all cases G5--G6 imply

    616(s_x+s_y)>=35(1-kappa_J)>0.                      (G7)

This transfers the qualitative pairs and their mixed binary cliques too.
Missing labels only reduce deletion; bounding exponents does not insert
new original classes. All report509 rows now hold for the exact-zero
support of the grouped family.

## The old source and finite-prefix repair are unchanged

The original old-only family remains supported on P. Choose the same
completed-and-charged source nu in its physical prime order. The source
construction is inherited from Michael Schroeder's *Nine Prime Divisors
in Odd Distinct Covering Systems*, edition1.0.1; the
[library entry](../../../../../Library/Arith/schroeder2026nine.md)
records attribution and the verification boundary.

The actual anchor phases, source lower bound, conditional caps, old-label
masks, reference orbits and infinite old tails in report517 are unchanged.
The transferred rows imply the same signed-price upper bound for the
comparison family's exact-zero support. Hence its positive-fibre source
mass is at least the same delta_p, the minimum of the worst-type bound
and report491's direct nonworst source separation.

Repair G2 by choosing one full extension of every finite prefix and one
CRT comparison residue per complete original d_i*n_Ri*n_Si. Keep each
numerical label, sigma_i and every outside coordinate literally fixed.
Use maximum of the prescribed depth and queried depth to preserve
unqueried first-root splits. This is precisely the repair of report518,
with a larger outside product. Original and comparison indicators agree
for every outside point off the same old exceptional union E.

Joint3/5 marginal domination and the physical-prime cylinder caps give

    nu(E)<=epsilon_p
      =2/3^11+2/5^7+(3/4)C_p/p^6
        +(3/8)sum_(q in{7,11,13,17,19},q!=p) C_q/q^4.

The retained exact scalar calculation proves delta_p-epsilon_p>1/20000.
Therefore

    nu({x:original later survival is positive})>1/20000. (G8)

This source is supported on old-only survivors. Finiteness of the original
family gives a finite CRT period in all actual prime coordinates; an
old positive fibre yields an uncovered integer. Neither the repair nor
the row transfer substitutes another family into the lower source bound.

## A positive threshold away from the saturated budget

Put kappa=616alpha_R alpha_S. If kappa<1, the weaker height-independent
mixed bound and G6 give

    616(s_x+s_y)>=35(1-kappa).

Every row, including the qualitative pairs and mixed cliques, is then
valid for strict s<theta, with

    theta=min(1/3696,35(1-kappa)/1232)>0.                (G9)

Thus report517's same upper certificate bounds the strict-theta bad
support too. The nonworst source argument uses1/77>=theta. The comparison
has theta-good source mass at least delta_p, and equality of fibres off
E transfers that bound to original theta-good source mass greater
than1/20000. Using the retained joint density cap
nu<=(27/2)H_old from report491 gives the separate quantitative corollary

    H_full(original survivors)>theta/270000.            (G10)

For two distinct primes r>=23,s>=29 other than(23,29), one has
(r-1)(s-1)>=660, hence kappa<=14/15<104/105. Equation G9 then allows
theta=1/3696, so the full original survivor density is greater than
1/997920000. The same bound holds for any grouped pair with
kappa<=104/105. This statement does not apply to the saturated baseline
R={23},S={29}, which retains G8 without a uniform threshold from G7.

For finite groups the saturated case is unique. Equality kappa=1 forces
alpha_R=1/22 and alpha_S=1/28. Every prime in R is at least23 by G1.
If its largest prime L exceeded23, the identity

    22 product_(r in R) r=23 product_(r in R)(r-1)

would have L dividing the left side but no factor on the right. Hence
R={23}. The same argument gives S={29}. All other admissible finite
groupings have the positive group-dependent bound G10.

For example R={31,89},S={29} gives alpha_R=119/2640 and kappa=119/120.
It satisfies G1 but exceeds104/105, and G9 gives theta=1/4224. This is
a sufficient threshold; it does not assert failure of a stronger bound.
There is no universal positive threshold over all finite groupings
established by G9.

## Evidence and remaining boundary

The numerical row certificates and report517/518 exact outputs are reused
at their existing scope. Their executables still bind the original
23/29 numerical model. This proof establishes inclusion of grouped
actual deletion quantities in that model; it does not claim those CLIs
already accept arbitrary prime groups. No new geometry, optimizer or
Lean verification is asserted.

The exact inherited prefix margins can be reproduced with

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite_prefix_template_source.py

The group transfer G3--G7 and threshold G9 are ordinary mathematical
deductions. Their hypotheses preserve the complete numerical labels,
one actual family and all original outside phases. G1 restricts total
reciprocal inventory: it does not cover every finite prime support.
G2 still restricts the old prefixes and their simultaneous selectors.
Removing either restriction, or resolving unrestricted Erdős#7, requires
new arguments.
