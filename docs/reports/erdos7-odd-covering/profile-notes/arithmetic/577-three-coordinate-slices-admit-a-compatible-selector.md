# Three-coordinate antichains admit the same periodic selector

## Box-slice theorem

For nonnegative integers N,A,B,C, let

    S={ (a,b,c) in Z_{≥0}^3 : a+b+c=N, a<=A, b<=B, c<=C },
    color(a,b,c)=b+2c mod3.

If S has at least three points, its colors are all of Z/3Z. Equivalently, a slice missing any one color has at most two points. Upper bounds greater than N can be truncated at N.

### General proof

Join two feasible points when one is obtained from the other by transferring one unit from one coordinate to another.

This graph is connected. If x and y are distinct feasible points, choose coordinates i and j with x_i>y_i and x_j<y_j. Replacing x by x−e_i+e_j preserves the coordinate sum and the box bounds: x_i>0 and x_j<y_j<=U_j. It reduces the L1 distance to y by two. Repeating reaches y through feasible points.

A connected graph with at least three vertices has a vertex x of degree at least two. Give coordinates a,b,c weights0,1,2 modulo3. Every feasible transfer i→j changes color by w_j−w_i, which is either1 or2. If two neighbors have different increments, x and those neighbors already exhibit all three colors.

Otherwise take two distinct transfers with the same increment delta. The three possible transfers having that increment form one directed three-cycle. Any two distinct edges of this cycle can be ordered i→j→k. Feasibility of the first gives x_i>0; feasibility of the second gives x_k<U_k. Consequently the direct transfer i→k is also feasible at the ORIGINAL x, irrespective of the intermediate coordinate. Its color increment is2delta, the other nonzero residue. Again the neighbors together with x exhibit all three colors.

This proves the theorem for arbitrary N and arbitrary box bounds. The argument does not assume that the slice is a line or contains an elementary triangle. The latter stronger shortcut is unnecessary.

## Exact limitation at four coordinate directions

The property “every box slice with at least three points contains all three colors” cannot hold for ANY three-coloring on the four-coordinate simplex, already at N=1. Its four points are the four unit vectors. Two must have the same color. Take these two and any third unit vector. The resulting three points have at most two colors. Set the upper bounds to1 on these three coordinate directions and0 on the fourth; the corresponding box slice is exactly the chosen three points and misses a color.

Thus the three-color selector argument with a uniform missing-color slice bound of two cannot extend unchanged to four coordinates. This is an obstruction to that selector property, not an arithmetic covering counterexample or an impossibility theorem for other selectors, larger incidence bounds, or other source constructions.

## Selector on a two-dimensional cofactor inventory

Fix three distinct primes p,q,r in Q={5,7,11,13,17,19}, a nonunit Q-smooth D coprime to pqr, and three fixed global integers r0,r1,r2 with pairwise distinct residues modulo D. The cofactor inventory is

    d_(a,b,c)=D p^a q^b r^c, a+b+c=N.

Allow arbitrary pure3 originals and arbitrary Q-only originals. Every other actual original has modulus3^e d_(a,b,c). At each inventory cofactor, require its actual projections at exponents e=0,1,2,3 to occupy at most one phase a_(a,b,c), including its Q-only original if present. At exponents e>=4 its actual projection must be one of the three global r0,r1,r2. Original ternary phases and all finite heights are arbitrary, and every full numerical modulus has one globally fixed phase.

Choose at each inventory node the selected Q phases

    {a_(a,b,c), if present} union {r_(b+2c mod3)}.

This may use an auxiliary phase or a missing cofactor label in the SELECTED Q input. This finite restriction is allowed explicitly and is used only to choose a law supported on a subset of the actual survivor. It does not insert a new original covering class or alter any original phase. At every other actual Q-only label select its actual phase. Every selected numerical modulus has at most two phases, so Report569 supplies one actual PA law nu with R_Q(nu)<=B and its density bound.

Fix the SAME x in the selected survivor V. A matching tail phase at any inventory node determines x modulo D, hence determines a unique possible global color j. For that j, the complete set of POTENTIAL matching indices is

    S_j(x)={a+b+c=N,
             0<=a<=v_p(x-r_j),
             0<=b<=v_q(x-r_j),
             0<=c<=v_r(x-r_j)}.

Valuations are truncated at N, and the fixed congruence x=r_j modD has already been imposed. This is exactly a box slice of the theorem. If it had at least three points, one would have color(a,b,c)=j. That periodic phase was selected there, contradicting x in V. Therefore at most two potential indices match; actual tail events, which may be missing, are only a subset.

At each selected Q point, at most two numerical cofactors can thus act. The complete pure3 source satisfies u<=2H3, and the complete e>=4 tail at any one cofactor has u-mass at most1/27. Consequently c(x)>=25/27. Report572 supplies the same fixed-u lift and numerical constants:

    R_P <= B+(27/25)(1+B)
        =6199418183523781383463/539719033471556471250
        <566/49.

The actual23/29 extension has the same Haar lower bound>1/37000. This is a two-dimensional indexing inventory of size(N+1)(N+2)/2. The coefficient bound is inherited; the new step is the box-slice selector theorem that proves the pointwise incidence premise.

No analogous claim is made for arbitrary tail projections, two compulsory shallow phases, or more coordinate directions. The selected phases are fixed before sampling x. General auxiliary selected restrictions remain necessary when the actual inventory has gaps.

## Actual 364-original example and source change

Take p=5,q=7,r=11,D=13,N=12 and global tail phases0,1,2. There are91 cofactors. Order their triples lexicographically, indexed j=0,...,90, and at every cofactor d_j use exactly four actual originals:

| ternary exponent e | Q phase modulo d_j | ternary phase modulo3^e |
|---|---|---|
|0|3|vacuous|
|4|1|j mod81|
|5|2|0|
|6|0|0|

These364 full numerical moduli are distinct, odd and nonunit. There are no pure3 originals, so u=H3. Set K=13·5^12·7^12·11^12.

For the old mandatory shallow selector {3} at every cofactor, the selected input has only row13 originals. Earlier5/7/11 coordinates are Haar. The row13 forbidden set is empty or root3, so its density is at most13/12 below the retained PA cap3/2. Later17/19 coordinates are Haar and every row has mass one. Thus the actual old PA law satisfies

    R_Q(nu0)<=(13/12)·157435/165888.

On A=[1 mod K], no old-coordinate projection to phase3 matches, so the row is Haar and nu0(A)=1/K>0. All91 depth4 originals match A; their j mod81 ternary phases exhaust all81 cells. Hence the actual fibre is empty on A. No joint law supported on U can retain nu0.

Now select the periodic second slot b+2c mod3. The selected input still has only row13 originals, whose forbidden root set is a subset of{0,1,2,3}. Every row has good mass at least9/13, so its normalized density is at most13/9<3/2. No PA mass loss occurs. The new actual law has

    R_Q(nu)<=(13/9)·157435/165888.

The box-slice theorem leaves at most two active cofactors. In this finite example each contains only depths4,5,6, so c>=1−2(3^-4+3^-5+3^-6)=703/729. Using R3(H3)=1/2, the one fixed-u lift has the complete-query upper

    R_P <= (13/9)r_H+[729/(2·703)](1+(13/9)r_H)
        =5457999593/2099146752
        =2.60010386972697... .

These are density-based upper bounds, not optimum claims. The new marginal comes from rebuilding the selected actual PA input, not from retaining the old dead-fibre marginal.

Every original has a private witness. For its cofactor d_(a,b,c) and Q color t in{0,1,2,3}, choose x_Q=t+d_(a,b,c) modulo K. Its valuations at5,7,11 truncated at12 are(a,b,c). Any same-color matching cofactor has exponents componentwise at most(a,b,c) with the same total12, hence equals that cofactor. Different colors are separated modulo13. Choose the required ternary residue by CRT. This witnesses only the chosen original, including when several depth4 originals share a ternary residue.

## Six-coordinate selectors: finite bounds and the direct-lift limitation

### Six-coordinate model

For six fixed coordinates, let X_N={a in Z_{>=0}^6:sum a_i=N}. A box slice is S_N(U)={a in X_N:a_i<=U_i}. A three-color selector chooses one of three fixed global tail phases at each numerical cofactor. One mandatory shallow phase occupies the other selected slot. A slice missing color j models the potential active cofactors at a point whose reference residue is global phase j.

A fixed nonunit reference divisor D may share primes with the six coordinates. For d_a=D product q_i^(a_i), the slice bounds are v_(q_i)(x-r_j)-v_(q_i)(D). Pairwise distinct global phases modulo D still ensure at most one possible j at a given x. Coprimality of D to all six primes is not required for this valuation statement.

### A uniform bound must be at least four

At N=1 the simplex consists of the six unit vectors. In ANY three-coloring, the least frequent color occurs at most twice. Set U_i=1 exactly at coordinates whose unit vector is not of that color and U_i=0 at the others. The resulting box slice has at least four points and misses that color.

More generally d directions force a missing-color slice of at least d-floor(d/3) at N=1. In particular every d>=4 rules out the unchanged missing-color<=2 property. This quantifies over arbitrary colorings, including choices depending on N; it is not limited to linear colorings.

This is a bound on a uniform-in-N selector certificate. It does not assert that every large-N coloring has the same lower bound, nor that any actual arithmetic survivor law has query norm exceeding a target.

### A finite uniform bound exists

Color a in X_N by grouping the residue of sum_(i=0)^5 i*a_i modulo7 into {0,1}, {2,3}, {4,5,6}. This gives one explicit three-coloring for every N.

A unit transfer between any two different coordinates changes that residue by a nonzero value modulo7. Six consecutive points on such a root-direction line have six distinct residues and omit only one residue. Each color group has at least two residues; therefore all three colors occur on every such six-point line.

Let T=sum U_i-N. If a nonempty box slice has N>=5, T>=5 and two bounds U_i,U_j>=5, it contains a six-point root-direction line. Indeed choose the sum s of these two coordinates in the nonempty integer interval

    max(5,N-sum_(k!=i,j)U_k) <= s <= min(U_i+U_j-5,N).

The other coordinates can realize N-s because their integer box realizes every sum between zero and their total upper bound. At this fixed other-coordinate assignment, the permitted interval for coordinate i has length at least5.

Consequently a slice missing any color has either N<5, T<5, or at most one upper bound>=5. In the first two cases its cardinality is at most binomial(9,5)=126, using a or the deficits U-a. In the last case choose five coordinates with bounds<=4; their values determine the sixth coordinate, so the cardinality is at most5^5=3125.

Thus this coloring has a uniform missing-color bound3125. This bounds the best possible uniform missing-color constant between4 and3125. Its sharp value is not determined here; the upper bound is a combinatorial result and is not claimed to pass the arithmetic continuation gate.

### The retained incidence consumer cannot use the six-coordinate bound

With the existing six-prime B and the complete pure-source caps R3<=1, u<=2 Haar, the h3 direct lift certificate, for 0<=M<27 so that the fibre-reserve denominator is positive, is

    C(M)=B+(1+B)/(1-M/27),
    B=432040125182653876501/86355045355449035400.

It beats566/49 exactly when

    M<62251906883410927926954/27706989537234114087851
      =2.2467943260220866... .

Only integer bounds M<=2 qualify. The six-coordinate lower bound M>=4 is already outside this range:

    C(3)=11.756518543406196...,
    C(4)=12.05014684747437... .

For comparison, Report574 already handles the whole through-e4 two-phase class with no incidence bound and arbitrary later phases. A larger incidence bound at that depth does not enlarge that positive class.

Even arbitrary reweighting of the pure source does not rescue this SAME M4,complete-tail-cap direct-lift envelope uniformly. Take the pure ternary comb with originals3^(e-1) modulo3^e for e=1,...,4. By [Report578](578-pure-prime-density-query-tradeoff-and-scalar-clip-boundary.md), every supported probability has A=R3>=31/32. There are41 surviving depth4 cells, hence M4(u)>=1/41. Descendants of a maximal depth4 cell give

    theta=sum_(e>=4)M_e(u)>=(3/2)M4(u)>=3/82.

The direct certificate retaining only incidence M=4 and these complete caps is

    B+A(1+B)/(1-4theta),

when its denominator is positive. It increases in A and theta. Even the relaxation that simultaneously substitutes their separate minima is at least

    380921733986167047569097/32239216932700973216000
      =11.815477242556392... >566/49.

This makes a finite-input statement over ALL pure sources, rather than merely checking normalized Haar. It does not assume that the two lower minima are simultaneously attainable.

The obstruction is still limited to that certificate. A phase-weighted selector can retain which tail phases actually carry the ternary mass; actual fibre unions can have substantial overlap; the actual Q query cost may be smaller than B; and a joint source can retain more than one scalar incidence bound. The finite geometric lower bound does not force these discarded quantities to attain their worst bounds simultaneously. No impossibility claim for such refinements or for actual noncoverage follows.

The [exact diagnostics](../../frontier/cover-geometry/six_direction_selector_boundary.py) and [data](../../frontier/cover-geometry/six_direction_selector_boundary.json) check all729 colorings at N=1, all42 modular line progressions, and the rational gate inequalities in6 named checks. The general box argument and arbitrary-source bounds above supply the quantifiers beyond those finite checks.

## Verification

Program: [three_coordinate_periodic_selector.py](../../frontier/cover-geometry/three_coordinate_periodic_selector.py).
Data: [three_coordinate_periodic_selector.json](../../frontier/cover-geometry/three_coordinate_periodic_selector.json).

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/three_coordinate_periodic_selector.py

Exit0;14 named checks. Exhaustive diagnostics cover23409 box slices for N=0,...,16 and702 local feasible-transfer cases. The actual example has364 independently phased labels; all364 private witnesses were tested against every original, totaling132496 congruence comparisons. The PA row bounds, dead source mass, finite fibre reserve and complete-query arithmetic are retained. The general proof supplies the arbitrary-N quantifier; no huge period or infinite original family is enumerated.

The ordinary graph argument supplies the general selector theorem. No new Lean verification or external novelty claim is made.
