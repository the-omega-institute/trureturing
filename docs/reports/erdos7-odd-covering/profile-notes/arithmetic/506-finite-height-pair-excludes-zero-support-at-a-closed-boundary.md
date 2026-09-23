# A finite-height pair excludes zero support at a closed boundary

Two actual old survivors with inventories(21,26,35) cannot both have zero later-fibre survival in any finite original family. Their closed geometric-budget relaxation nevertheless has minimum zero. The distinction comes from the strictly smaller finite mixed budget and is useful for qualitative noncoverage without a height-independent positive threshold.

Among the190 representative capacity triples retained in[report500](500-a-binary-support-survives-1608-triple-exclusions.md), this is the only type whose zero feasibility disappears for every finite exponent cutoff: the other189 have exact zero witnesses already in the height3 capacity relaxation. This statement classifies those190 retained numerical representatives, not every possible original pair or its arithmetic realizability.

The named type occurs on7874 pairs in the complete20076-profile middle chart. Exactly nine occur in each retained support of reports500 and501. Their symmetry orbit has only144 edges, so the full same-capacity class supplies a larger input for subsequent zero-support optimization. All conclusions here are ordinary proofs and exact rational checks, with no Lean verification.

## Closed minimum zero and strict finite survival

Fix two old-only survivors x,y from the same finite original family and the same two-center interface. Here every modulus has the form d*23^j*29^k with d supported on the declared old primes; each old residue is one of the two declared centre residues modulo d. All complete numerical moduli are pairwise distinct and greater than one, so each d*23^j*29^k carries at most one original congruence class. The old-label inventory includes d=1. Additional prime directions or unrestricted old-centre choices are not included in this statement. Their individual old-label inventories are at most21 and26, and their common-selector joint inventory is at most35. Every complete numerical label has one old selector, shared across both points. New-coordinate phases and selectors may differ between different complete labels.

For new primes23,29, let t_x,t_y be22 times the actual pure23 union deletion fractions, and let u_x,u_y be28 times their pure29 counterparts. The closed necessary constraints are

    0<=t_x<=21, 0<=t_y<=22, t_x+t_y<=35,
    0<=u_x<=21, 0<=u_y<=26, u_x+u_y<=35.                 (F1)

Increasing axis deletion decreases the pure survivor products. Each axis can be extended within these bounds to spend total35. Thus the minimum total survivor product is obtained on

    t=(a,35-a), a in[13,21],
    u=(b,35-b), b in[9,21].                              (F2)

Subtract the closed joint mixed budget35 and define

    g(a,b)=(22-a)(28-b)+(a-13)(b-7)-35.

This is affine in each variable separately. Its four corner values are

| a | b | g(a,b) |
| ---: | ---: | ---: |
| 13 | 9 | 136 |
| 13 | 21 | 28 |
| 21 | 9 | 0 |
| 21 | 21 | 84 |

Every interior value is a convex combination of those four values, so the closed minimum is0. At(a,b)=(21,9), the axis vectors are(21,14),(9,26), and the residual vector is(19,16). It also obeys the mixed singleton bounds21,26 and the joint bound35. Therefore the stronger max-clipping relaxation of[report481](481-individual-mixed-budgets-strengthen-two-fibre-certificates.md) has closed minimum0 as well.

Now use finiteness. Let J,K bound all23 and29 exponents in the actual original family, including mixed labels, and put

    c23=1-23^(-J), c29=1-29^(-K).

The sum of actual mixed-cylinder activity over both points is at most

    35*c23*c29/616.

This is the finite double geometric sum, with one common selector per original numerical label. If s_x,s_y are the later-fibre survivor fractions, the union bound and the preceding g>=0 give

    616(s_x+s_y)
      >=(22-t_x)(28-u_x)+(22-t_y)(28-u_y)-35*c23*c29
      >=35(1-c23*c29)>0.                                (F3)

Missing classes only decrease the mixed deletion bound. The cutoff may be padded to J,K>=1 when a new prime is absent. Because the points avoid all old-only classes, positive later-fibre Haar supplies an original uncovered integer by finite-period CRT.

The bound depends on the actual cutoffs and tends to0 as they grow. Thus F3 forbids a pair of zero-survival old points under a hypothesized covering. It does not supply a uniform theta=1/3696 and does not create an additional edge in the existing theta-bad graph.

## What is unique among the190 retained representatives

Report500 supplies one certified capacity threshold(q,r,N) for every unordered load-class pair20<=q<=r<=38, totaling190. The present certificate retains explicit rational vectors for189 of them at J=K=3. Write

    c23=12166/12167, c29=24388/24389.

Each witness satisfies

    0<=t_i<=min(22,c23*Q_i), sum(t)<=c23*N,
    0<=u_i<=min(28,c29*Q_i), sum(u)<=c29*N,
    R_i=(22-t_i)(28-u_i)<=c23*c29*Q_i,
    sum(R)<=c23*c29*N.                                  (F4)

Setting the relaxed mixed deletion equal to R gives zero survivor in this finite-height numerical envelope. The consumer checks every inequality exactly, rather than trusting an optimizer's claimed minimum. These189 witnesses have strict slack relative to every positive unscaled geometric inventory and rule out excluding their representative type solely by replacing infinite geometric budgets with finite ones.

The unique remaining representative is(21,26,35). F3 excludes zero for every finite J,K, while F2 exhibits a closed zero. Its status therefore differs from the other189 within this declared numerical test. The witnesses in F4 are not original families; further phase or shared-label constraints remain available.

## Complete same-type chart census

Use the same six-anchor chart, reference(2,7,3,4), and index order as reports500 and501. The first three old coordinates3,5,7 are split, the last four11,13,17,19 common. Signed split entries represent +f=(f,1), -f=(1,f), and0=(1,1), with signed3 nonzero. For a profile s,

    Q(s)=(product(max(1,s_split))
           +product(max(1,-s_split))-1)*product(s_common).

The finite Q<=38 chart has23408 profiles, of which20076 have20<=Q<=38. Exactly432 middle profiles have Q=21 and814 have Q=26. Their complete Cartesian pair domain has351648 elements.

For two such profiles s,t, write I for the product of the four common-coordinate minima, and C for the sum of the two opposite-center split-box intersection sizes. The shared-selector capacity is

    N(s,t)=Q(s)+Q(t)-I*(C-2).                             (F5)

The Boolean expansion used in report500 proves F5. The consumer checks all16 one-label Boolean patterns, then evaluates the complete351648-pair domain. It finds7874 pairs with capacity exactly35 and independently recomputes every one from the literal old exponent labels and their two activation masks.

This is a complete census of the named(Q=21,Q=26,N=35) type in the finite middle chart. It is not a census of all qualitative forbidden pairs, all overflowing profiles, or all original families. Types with stronger capacities remain covered by their applicable prior results.

Every listed pair is a zero-support forbidden edge. If both endpoints of its upward-support image came from zero-survival actual old points below them in labelled-box order, their actual individual and joint inventories would be at most21,26,35. The monotone capacity argument and F3 would contradict simultaneous zero survival. All endpoints must come from the same original family; arbitrary old-point laws are not substituted.

## Nine retained occurrences and the larger class

The report500 support and its two-point report501 repair contain the same nine named-type edges:

    {1014,14515},
    {4670,12949}, {4670,12950}, {4670,14513}, {4670,14515},
    {5640,12949}, {5640,12950}, {5640,14513}, {5640,14515}.

The report501 removals4405,4407 are not endpoints. The exact input hashes bind both supports and their declared index order.

Simultaneous permutations of the three split coordinates, permutations of the four common coordinates, and global A/B exchange preserve the labelled capacity type. Applying all these transformations to the nine retained edges gives2592 eligible transformations and144 distinct chart edges. The full same-capacity census has7730 further edges. The7874-edge set is therefore a full capacity-type class, not merely the symmetry orbit of the nine support occurrences.

The original supports were certified against positive-threshold exclusions. Their containing these zero-support edges does not invalidate those theta-support checks. Under an assumed full covering, however, every actual old-only survivor has later survival0; a zero-support optimization must also enforce these qualitative edges.

A future same-source upper bound on all such zero supports below m7 would contradict full coverage directly. No uniform positive theta is needed for that qualitative implication. This report supplies the valid edges and their exact chart domain; it does not compute such a global upper bound, convert an auxiliary support into an actual source, or certify a repaired support as globally optimal.

## Reproduction

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/finite_height_qualitative_pair.py

The standard-library consumer pins the canonical report500 result and support certificate and the report501 result. It checks the189 finite-budget witnesses, the closed four-corner certificate, the complete profile order, all351648 named load-class pairs, all7874 literal capacities, both supports' nine occurrences and their complete144-edge symmetry orbit. A default run compares regenerated output with the adjacent JSON. The all-height conclusion is the ordinary geometric-series proof F3, not an extrapolation from height3 calculations.
