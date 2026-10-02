# A nonnormal index-72 cover and an N=24 degree-(8,9) packet

## Scope and theorem

The six-sector Coxeter construction for the pure three-cycle degree-(8,9) packet uses
W=<a,b,c,d | a²=b²=c²=d²=1, (ab)^4=(bc)^9=(cd)^3=1, [a,c]=[a,d]=[b,d]=1>.
Let W+ be its determinant/orientation-preserving subgroup. The previous normal-quotient obstruction (PR #12096) does not apply to arbitrary finite-index subgroups. This note gives an explicit torsion-free nonnormal subgroup Gamma < W+ of index 72, so the six-sector quotient has exactly 24 target tetrahedra.

This proves existence of an N=24 member of the six-sector [4,9,3] Coxeter-sector family. It makes no claim about arbitrary pseudo-simplicial pairings outside that family, and no minimality claim beyond the known divisibility 24 | N.

## Orientation presentation

Put x=ab, y=bc, z=cd. Reidemeister–Schreier gives
W+=<x,y,z | x^4=y^9=z^3=(xy)^2=(yz)^2=(xyz)^2=1>.
Here xy=ac, yz=bd, and xyz=ad. The three maximal finite standard parabolics have orientation subgroups
<x,yz> ≅ D8, <xy,z> ≅ S3, and <y> ≅ C9, of orders 8, 6, and 9. The middle group is S3, not cyclic.

## Exact PSL2(71) certificate

Over F71 define
X=[[2,7],[23,10]], Y=[[0,70],[1,30]], Z=[[47,66],[35,25]],
with U=XY=[[7,66],[10,64]], V=YZ=[[36,46],[32,35]], T=XYZ=[[12,53],[12,59]].
All determinants are 1 and direct multiplication gives
X^4=Y^9=Z^3=-I and U^2=V^2=T^2=-I in SL2(F71). Thus their projective classes define rho:W+ -> PSL2(F71). The projective orders are 4,9,3,2,2,2. In PSL2(F71), [V][X][V]=[X]^-1 and [U][Z][U]=[Z]^-1; at the SL2 representative level these equalities may carry the central sign. Since V != X^2 projectively, the finite parabolic images are D8, S3, and C9.

The word P=X Z Y^-3=[[56,49],[31,17]] has determinant 1, trace 2, and is not I. Its projective class is a nontrivial unipotent of order 71, fixing one point and acting as a single 71-cycle on the remaining points. A point stabilizer in PSL2(F71) has order 71(71-1)/2=2485. Since 4 does not divide 2485, X fixes no point, so X moves the fixed point of P into its 71-cycle. Hence rho(W+) is transitive on P1(F71), which has 72 points.

Let B_infty be the stabilizer of infinity and Gamma=rho^-1(B_infty). Then [W+:Gamma]=72.

## Torsion-freeness and nonnormality

Every finite-order element of a Coxeter group is conjugate into a finite standard parabolic. If the conjugator is orientation reversing, left-multiply it by a reflection in that finite parabolic to obtain an orientation-preserving conjugator without leaving the parabolic. Hence every finite-order element of W+ is W+-conjugate into one of D8, S3, C9.

Any PSL2(F71) element fixing a projective point lies in a conjugate of the Borel B and has order dividing 2485. Every nonidentity element in the three finite images has order 2, 3, 4, or 9, so acts fixed-point-freely. Therefore Gamma is torsion-free.

Gamma is genuinely nonnormal: conjugating the fixed point of P to infinity produces a nonidentity element of rho(W+) in B_infty; a normal point stabilizer in a transitive action would be the kernel and act trivially.

## The six-sector quotient has N=24

Let K=<c,d> ≅ S3, |K|=6. Since [W+:Gamma]=72, [W:Gamma]=144. The coarsened tetrahedra are indexed by Gamma\W/K. Torsion-freeness makes every right K-orbit free, so
N=|Gamma\W/K|=[W:Gamma]/|K|=144/6=24.

The six-sector development and face/link checks in merged PR #12065 apply to every finite-index torsion-free subgroup. Therefore this quotient is connected, orientable, compact with totally geodesic boundary; coarsening gives complete tetrahedral face pairings, low degree 8, high degree 9, and boundary components of genus at least two. The result is a valid N=24 packet in the six-sector family.

The argument does not claim that every arbitrary 24-tetrahedron pseudo-simplicial pairing is Coxeter-sector-derived, and does not alter the scoped normal index-72 obstruction of PR #12096.

## Verification

The companion verifier verify_cycle9_psl71.py is deterministic and standard-library-only. It checks all matrix identities, projective orders, exact transitivity, finite subgroup orders, and cycle structures X=4^18, Y=9^8, Z=3^24, and XY=YZ=XYZ=2^36, and every nonidentity element in each of the D8, S3, and C9 images is fixed-point-free on P1(F71). It uses no random search, floating point, or normal-quotient assumption.


## Sources and scope

The [4,9,3] Coxeter presentation and six-sector face/link construction are the project’s merged reference in PR #12065, docs/develop/theory/CFMP_CYCLE_DEGREE9.md. The finite-subgroup input used here is the Tits theorem cited by the project’s finite-quotient reference, docs/develop/theory/CFMP_CYCLE_DEGREE9_FINITE_QUOTIENT.md: finite-order elements of a Coxeter group are conjugate into finite standard parabolic subgroups. A precise primary account is Davis, *The Geometry and Topology of Coxeter Groups*, Theorem 12.3.4(i), p. 251, with Corollary D.2.9, p. 446, attributing the result to Tits (https://people.math.osu.edu/davis.12/davisbook.pdf); the project also records Howlett’s exposition (https://www.maths.usyd.edu.au/u/ResearchReports/Algebra/How/1997-6.html). The orientation-presentation rewrite is the direct Reidemeister–Schreier calculation shown above; a general adjacent-reflection-product precedent is Conder–Martin, *Cusps, triangle groups and hyperbolic 3-folds*, J. Austral. Math. Soc. 55 (1993), pp. 152–153 and 160–161 (https://doi.org/10.1017/S1446788700032018). This note applies those cited inputs and makes no Lean claim.
